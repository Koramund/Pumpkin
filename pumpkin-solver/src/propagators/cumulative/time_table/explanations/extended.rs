use crate::basic_types::cumulative_literal::{CumulativeExtendedType, CumulativeLiteral, MapToLiteral};
use crate::basic_types::PropositionalConjunction;
use crate::engine::propagation::{PropagationContext, PropagationContextMut, Propagator, ReadDomains};
use crate::engine::EmptyDomain;
use crate::predicates::Predicate;
use crate::propagators::cumulative::time_table::explanations::big_step::{create_big_step_conflict_explanation, create_big_step_predicate_propagating_task_lower_bound_propagation, create_big_step_predicate_propagating_task_upper_bound_propagation, create_big_step_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::naive::{create_naive_conflict_explanation, create_naive_predicate_propagating_task_lower_bound_propagation, create_naive_predicate_propagating_task_upper_bound_propagation, create_naive_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::pointwise::{create_pointwise_conflict_explanation, create_pointwise_predicate_propagating_task_lower_bound_propagation, create_pointwise_predicate_propagating_task_upper_bound_propagation, create_pointwise_propagation_explanation};
use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessOrEqualMinimumPropagator;
use crate::propagators::{ReifiedPropagator, ResourceProfile, Task};
use crate::variables::{IntegerVariable, Literal};
use crate::pumpkin_assert_simple;
use std::collections::HashMap;
use std::ops::Not;
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};


/// TODO create a new solver parameter that can be used to denote which underlying system extended resolution should utilise.

pub(crate) static CUMULATIVE_TO_LITERAL: LazyLock<Mutex<HashMap<MapToLiteral, Literal>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(crate) fn propagate_lower_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
    underlying_type: CumulativeExtendedType,
) -> Result<(), EmptyDomain> {
    let global_id = propagating_task.start_variable.get_id();
    let mut cache = CUMULATIVE_TO_LITERAL.lock().unwrap();

    for profile in profiles {
        // note this may actually not be used but bad architecture choices requires this to be done here :(
        let pointwise_timepoint = profile.end.min(
            context.lower_bound(&propagating_task.start_variable) + propagating_task.processing_time
                - 1,
        );
        
        let mut explanation = create_support(&context.as_readonly(), profile, pointwise_timepoint, underlying_type);
        explanation.add(create_pointwise_predicate_propagating_task_lower_bound_propagation(propagating_task, Some(pointwise_timepoint)));

        let mut is_first = false;
        
        let key = MapToLiteral::new(true, global_id, convert_profile_to_raw_ids(profile));
        let literal = cache.entry(key).or_insert_with(|| {is_first = true; context.create_new_literal(None)});

        pumpkin_assert_simple!(context.lower_bound(literal) >= 0, "We are about to set this literal to true so there is no way it can currently be false.");
        context.assign_literal(literal, true, explanation)?;
        
        // Start >= min(end of conflicts)

        if is_first {
            let true_propagator = LargerOrEqualMinimumPropagator::new(
                propagating_task.start_variable.clone().scaled(1),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect());
            let false_propagator = LessOrEqualMinimumPropagator::new(
                propagating_task.start_variable.clone().scaled(1),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect());
            
            let mut new_propagators = CumulativeLiteral::new(
                ReifiedPropagator::new(
                    true_propagator,
                    *literal),
                ReifiedPropagator::new(
                    false_propagator,
                    literal.not()
                )
            );

            pumpkin_assert_simple!(context.lower_bound(literal) >= 1, "Propagating propagators we just created requires the literal to be set to true");
            new_propagators.prop1.initialise_at_root(&mut context.as_initialisation_context()).expect("Prop 1 failed to initialize, was the timetable consistent?");
            new_propagators.prop2.initialise_at_root(&mut context.as_initialisation_context()).expect("Prop 2 failed to initialize, was the timetable consistent?");
            
            context.with_reification(*literal);
            new_propagators.prop1.propagator.propagate_directly(context).expect("The timetable was already inconsistent, therefore propagation failed here and we did not deal with it.");
            context.without_reification();
            
            context.cumulative_literals.push(new_propagators)
        }
        
    }

    Ok(())
}



pub(crate) fn propagate_upper_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
) -> Result<(), EmptyDomain> {
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
/// pointwise, bigstep, naive all take different parameters for this.
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