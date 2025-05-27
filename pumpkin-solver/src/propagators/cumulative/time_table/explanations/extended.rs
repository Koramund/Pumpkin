use crate::basic_types::cumulative_literal::{CumulativeExtendedType, CumulativeLiteral, MapToLiteral};
use crate::basic_types::{Inconsistency, PropagationStatusCP, PropositionalConjunction};
use crate::engine::propagation::{PropagationContext, PropagationContextMut, Propagator, ReadDomains};
use crate::engine::EmptyDomain;
use crate::predicates::Predicate;
use crate::propagators::cumulative::time_table::explanations::big_step::{create_big_step_conflict_explanation, create_big_step_predicate_propagating_task_lower_bound_propagation, create_big_step_predicate_propagating_task_upper_bound_propagation, create_big_step_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::naive::{create_naive_conflict_explanation, create_naive_predicate_propagating_task_lower_bound_propagation, create_naive_predicate_propagating_task_upper_bound_propagation, create_naive_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::pointwise::{create_pointwise_conflict_explanation, create_pointwise_predicate_propagating_task_lower_bound_propagation, create_pointwise_predicate_propagating_task_upper_bound_propagation, create_pointwise_propagation_explanation};
use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::{ReifiedPropagator, ResourceProfile, Task};
use crate::pumpkin_assert_simple;
use crate::variables::{IntegerVariable, Literal, TransformableVariable};
use std::collections::HashMap;
use std::ops::Not;
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};
use itertools::Itertools;

/// TODO create a new solver parameter that can be used to denote which underlying system extended resolution should utilise.

pub(crate) static CUMULATIVE_TO_LITERAL: LazyLock<Mutex<HashMap<MapToLiteral, Literal>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(crate) static LITERAL_TO_PROPAGATORS: LazyLock<Mutex<HashMap<Literal, CumulativeLiteral>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

/// This is an abstraction layer to hide behaviour between when it is the first propagation or a repeated propagation.
/// It guarantees that after being called the bounds of the propagating task have been updated in accordance to bound and the polarity of the literal.
/// In the current timetable API it does not support failure of the propagation and or initialization.
/// This is because the timetable itself contains the relevant information on whether a conflict occurs.
fn propagate_abstract<Var: IntegerVariable + 'static>(context: &mut PropagationContextMut, propagating_task: &Rc<Task<Var>>, profile: &&ResourceProfile<Var>, is_first: bool, literal: &mut Literal, bound: i32) -> Result<(), EmptyDomain> {    
    if is_first {
        let mut new_propagators = configure_new_literal(context, *literal, profile, propagating_task);
        init_propagators(context, *literal, &mut new_propagators).expect("initialization failed.");
        let _ = LITERAL_TO_PROPAGATORS.lock().unwrap().insert(*literal, new_propagators.clone());
        propagate_internal(context, *literal, &new_propagators, bound)?;
        context.cumulative_literals.push(new_propagators);
    } else {
        let map = LITERAL_TO_PROPAGATORS.lock().unwrap();
        let propagators = map.get(literal).expect("Since it is not the first time this literal is queried it should have a key in this map");
        propagate_internal(context, *literal, propagators, bound)?;
    }
    Ok(())
}

/// This function actually applies the propagation on the propagated task via the new propagators.
/// It does this by manually setting reification and then calling propagate on the underlying propagators.
/// It promises to return context with the correct ID set and no active reification.
fn propagate_internal(context: &mut PropagationContextMut, literal: Literal, propagators: &CumulativeLiteral, bound:i32) -> Result<(), EmptyDomain> {
    let cur_id = context.propagator_id;

    let result: PropagationStatusCP;
    if context.is_literal_true(&literal) {
        context.with_reification(literal);
        context.propagator_id = propagators.lb_id;
        result = propagators.lb_propagator.propagator.propagate_directly(context, bound);
    } else {
        pumpkin_assert_simple!(context.is_literal_false(&literal), "Propagating propagators with reification requires the literal to be set, it is currently undefined, note the if statement above.");
        context.with_reification(literal.not());
        context.propagator_id = propagators.ub_id;
        result = propagators.ub_propagator.propagator.propagate_directly(context, bound);
    }
    
    match result {
        Err(Inconsistency::EmptyDomain) => {return Err(EmptyDomain)}  // timetable only detect overflow conflicts, therefore an empty domain is still possible.
        Err(_) => {panic!("This propagation function is not allowed to raise a conflict.")}
        _ => {}
    }
    
    context.without_reification();
    context.propagator_id = cur_id;
    Ok(())
}

fn init_propagators(context: &mut PropagationContextMut, literal: Literal, propagators: &mut CumulativeLiteral) -> Result<(), EmptyDomain> {
    pumpkin_assert_simple!(context.is_fixed(&literal), "Propagating propagators we just created requires the literal to be set to true");
    propagators.lb_propagator.initialise_at_root(&mut context.as_initialisation_context(propagators.lb_id)).expect("Prop 1 failed to initialize, did reify mess up?");
    propagators.ub_propagator.initialise_at_root(&mut context.as_initialisation_context(propagators.ub_id)).expect("Prop 2 failed to initialize, did reify mess up?");
    Ok(())
}

fn configure_new_literal<Var: IntegerVariable + 'static>(context: &mut PropagationContextMut, lit: Literal, profile: &ResourceProfile<Var>, propagating_task: &Rc<Task<Var>>) -> CumulativeLiteral {
    CumulativeLiteral::new(
        ReifiedPropagator::new(
            LargerOrEqualMinimumPropagator::new(
                propagating_task.start_variable.clone().scaled(1),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect()),
            lit),
        ReifiedPropagator::new(
            // TODO yo do these offsets match?
            LargerOrEqualMinimumPropagator::new(
                propagating_task.start_variable.offset(propagating_task.processing_time).scaled(-1),
                profile.profile_tasks.iter().map(|x| x.start_variable.scaled(-1)).collect()),
            lit.not()),
        context.pop_new_propagator_id(),
        context.pop_new_propagator_id()
    )
}

pub(crate) fn propagate_lower_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
    underlying_type: CumulativeExtendedType,
) -> Result<(), EmptyDomain> {
    let global_id = propagating_task.start_variable.get_id();
    let mut cache = CUMULATIVE_TO_LITERAL.lock().unwrap();

    for profile in profiles {
        let pointwise_timepoint = profile.end.min(
            context.lower_bound(&propagating_task.start_variable) + propagating_task.processing_time
                - 1,
        );

        let mut explanation = create_support(&context.as_readonly(), profile, pointwise_timepoint, underlying_type);
        explanation.add(create_extended_predicate_propagating_task_lower_bound_propagation(context.as_readonly(), propagating_task, profile, Some(pointwise_timepoint), underlying_type));

        let key = MapToLiteral::new(global_id, convert_profile_to_raw_ids(profile));
        let mut is_first = false;
        let literal = cache.entry(key).or_insert_with(|| {is_first = true; context.pop_new_literal()});
        
        context.assign_literal(literal, true, explanation)?;
     
        let bound: i32 = profile.end+1;
        propagate_abstract(context, propagating_task, profile, is_first, literal, bound)?;
        pumpkin_assert_simple!(context.lower_bound(&propagating_task.start_variable) >= bound, "Propagation did not happen in accordance to the timetable")
    }
    Ok(())
}

pub(crate) fn propagate_upper_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
    underlying_type: CumulativeExtendedType,
) -> Result<(), EmptyDomain> {
    let global_id = propagating_task.start_variable.get_id();
    let mut cache = CUMULATIVE_TO_LITERAL.lock().unwrap();

    for profile in profiles {
        let pointwise_timepoint = profile.start
            .max(context.upper_bound(&propagating_task.start_variable));
        
        let mut explanation = create_support(&context.as_readonly(), profile, pointwise_timepoint, underlying_type);
        explanation.add(create_extended_predicate_propagating_task_upper_bound_propagation(context.as_readonly(), propagating_task, profile, Some(pointwise_timepoint), underlying_type));

        
        let key = MapToLiteral::new(global_id, convert_profile_to_raw_ids(profile));
        let mut is_first = false;
        let literal = cache.entry(key).or_insert_with(|| {is_first = true; context.pop_new_literal()});

        context.assign_literal(literal, false, explanation)?;

        // Remember the variables are negatively scaled
        let bound: i32 = -profile.start;
        propagate_abstract(context, propagating_task, profile, is_first, literal, bound)?;
        pumpkin_assert_simple!(context.upper_bound(&propagating_task.start_variable) <= profile.start - propagating_task.processing_time, "Propagation did not happen in accordance to the timetable");

    }

    Ok(())
}

/// TODO note that this blindly assumes that start variables are therefore the actual variables from the direct model.
/// TODO In the same reasoning this implementation assumes that variables encoding end_times for that reason are just offsets of those original variables.
fn convert_profile_to_raw_ids<Var: IntegerVariable + 'static>(profile: &ResourceProfile<Var>) -> Vec<u32> {
    profile.profile_tasks.iter().map(|x| x.start_variable.get_id()).collect()
}

/// Given a resource profile, this function should create the explanation for setting the literal.
/// Note that this function is (almost) agnostic to lower and upper bound variations (pointwise!)
/// Therefore, after calling this function one should add their lower/upper bound predicate for the shifting task.
fn create_support<Var: IntegerVariable + 'static>(
    context: &PropagationContext,
    profile: &ResourceProfile<Var>,
    time_point: i32,
    underlying_type: CumulativeExtendedType,
) -> PropositionalConjunction {

    match underlying_type {
        CumulativeExtendedType::Naive => {create_naive_propagation_explanation(profile, *context)}
        CumulativeExtendedType::BigStep => {create_big_step_propagation_explanation(profile)}
        CumulativeExtendedType::PointWise => {create_pointwise_propagation_explanation(time_point, profile)}
    }
}


// /// Creates the propagation explanation using the extended approach (see
// /// [`CumulativeExplanationType::extended`])
// pub(crate) fn create_extended_propagation_explanation<Var: IntegerVariable + 'static>(
//     time_point: i32,
//     profile: &ResourceProfile<Var>,
// ) -> PropositionalConjunction {
//
// }

/// Creates the conflict explanation using the point-wise approach (see
/// [`CumulativeExplanationType::pointwise`])
/// Note that there is no direct way for extended resolution to be utilized as a conflict variable in this instance.
/// As these variables are always proxies for actually incrementing a variable.
/// Therefore we utilize the pointwise method
/// TODO are there interesting variations to this, if we do big step supports it may make sense to do these as big step conflicts as well?
pub(crate) fn create_extended_conflict_explanation<Var: IntegerVariable + 'static, Context: ReadDomains + Copy>(
    context: Context,
    conflict_profile: &ResourceProfile<Var>,
    underlying_type: CumulativeExtendedType,
) -> PropositionalConjunction {
    match underlying_type {
        CumulativeExtendedType::Naive => {create_naive_conflict_explanation(conflict_profile, context)},
        CumulativeExtendedType::BigStep => {create_big_step_conflict_explanation(conflict_profile)},
        CumulativeExtendedType::PointWise => {create_pointwise_conflict_explanation(conflict_profile)},
    }
}

/// This returns the predicate to be used in the original reason when updating the lower bound of that same variable
/// AKA it is the predicate showing that the task to be moved is constrained enough to overlap with the mandatory parts of the profile.
/// TODO actually just do this bs after calling the create_support thing
/// pointwise, big step, naive all take different parameters for this.
pub(crate) fn create_extended_predicate_propagating_task_lower_bound_propagation<Var>(
    context: PropagationContext,
    task: &Rc<Task<Var>>,
    profile: &ResourceProfile<Var>,
    time_point: Option<i32>,
    underlying_type: CumulativeExtendedType,
) -> Predicate
where
    Var: IntegerVariable + 'static,
{
    match underlying_type {
        CumulativeExtendedType::Naive => {create_naive_predicate_propagating_task_lower_bound_propagation(context, task)}
        CumulativeExtendedType::BigStep => {create_big_step_predicate_propagating_task_lower_bound_propagation(task, profile)}
        CumulativeExtendedType::PointWise => {create_pointwise_predicate_propagating_task_lower_bound_propagation(task, time_point)}
    }
}

pub(crate) fn create_extended_predicate_propagating_task_upper_bound_propagation<Var>(
    context: PropagationContext,
    task: &Rc<Task<Var>>,
    profile: &ResourceProfile<Var>,
    time_point: Option<i32>,
    underlying_type: CumulativeExtendedType,
) -> Predicate
where
    Var: IntegerVariable + 'static,
{
    match underlying_type {
        CumulativeExtendedType::Naive => {create_naive_predicate_propagating_task_upper_bound_propagation(context, task)}
        CumulativeExtendedType::BigStep => {create_big_step_predicate_propagating_task_upper_bound_propagation(task, profile, context)}
        CumulativeExtendedType::PointWise => {create_pointwise_predicate_propagating_task_upper_bound_propagation(task, time_point)}
    }
}