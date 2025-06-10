use crate::basic_types::cumulative_literal::{CumulativeExtendedType, CumulativeLiteral, MapToLiteral};
use crate::basic_types::{Inconsistency, PropositionalConjunction};
use crate::engine::propagation::{PropagationContext, PropagationContextMut, Propagator, ReadDomains};
use crate::engine::EmptyDomain;
use crate::predicates::Predicate;
use crate::propagators::cumulative::time_table::explanations::big_step::{create_big_step_conflict_explanation, create_big_step_predicate_propagating_task_lower_bound_propagation, create_big_step_predicate_propagating_task_upper_bound_propagation, create_big_step_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::naive::{create_naive_conflict_explanation, create_naive_predicate_propagating_task_lower_bound_propagation, create_naive_predicate_propagating_task_upper_bound_propagation, create_naive_propagation_explanation};
use crate::propagators::cumulative::time_table::explanations::pointwise::{create_pointwise_conflict_explanation, create_pointwise_predicate_propagating_task_lower_bound_propagation, create_pointwise_predicate_propagating_task_upper_bound_propagation, create_pointwise_propagation_explanation};
use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessThanMinimumPropagator;
use crate::propagators::{ReifiedPropagator, ResourceProfile, Task};
use crate::pumpkin_assert_simple;
use crate::variables::{AffineView, IntegerVariable, Literal, TransformableVariable};
use std::collections::HashMap;
use std::ops::Not;
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};

/// TODO create a new solver parameter that can be used to denote which underlying system extended resolution should utilise.

pub(crate) static CUMULATIVE_TO_LITERAL: LazyLock<Mutex<HashMap<MapToLiteral, Literal>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(crate) static LITERAL_TO_PROPAGATORS: LazyLock<Mutex<HashMap<Literal, LargerOrEqualMinimumPropagator<AffineView, AffineView>>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(crate) fn propagate_lower_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
    underlying_type: CumulativeExtendedType,
) -> Result<(), EmptyDomain> {
    let global_id = propagating_task.start_variable.get_id();
    let mut cache = CUMULATIVE_TO_LITERAL.lock().unwrap();

    for profile in profiles {
        // Due to the more optimal propagation strength per profile it can be that we are supposed to skip over other profiles.
        if context.lower_bound(&propagating_task.start_variable) >= profile.end + 1 {
            continue;
        }
        
        let pointwise_timepoint = profile.end.min(
            context.lower_bound(&propagating_task.start_variable) + propagating_task.processing_time
                - 1,
        );
        
        let mut explanation = create_support(&context.as_readonly(), profile, pointwise_timepoint, underlying_type);
        explanation.add(create_extended_predicate_propagating_task_lower_bound_propagation(context.as_readonly(), propagating_task, profile, Some(pointwise_timepoint), underlying_type));
        
        let key = MapToLiteral::new(true, global_id, convert_profile_to_raw_ids(profile));
        let mut is_first = false;
        let literal = cache.entry(key).or_insert_with(|| {is_first = true; context.pop_new_literal()});
        
        // Originally we wanted to add assertions here but it actually a makes a lot more sense to not.
        // This way this function can error out on the empty domain in the case the variable was set wrong.
        // If the literal is set to false then this should rightfully raise a conflict.
        // TODO If the literal was set to true then something has gone wrong as we propagate optimally. (delete this assertion in the non optimal case where propagate directly goes to a bound)
        
        // if context.is_literal_true(literal) {
        //     dbg!(context.lower_bound(&propagating_task.start_variable), profile.end+1, profile.profile_tasks.iter().map(|x| context.lower_bound(&x.start_variable) + x.processing_time).collect_vec());
        // }
        // pumpkin_assert_simple!(!context.is_literal_true(literal), "The literal was already set to true, are your propagators strong enough?");

        let cur_id = context.propagator_id;
        if is_first {
            pumpkin_assert_simple!(!context.is_literal_fixed(literal), "When given a meaning a literal should not have had a value from before");
            literal.make_decidable();
            let true_propagator = LargerOrEqualMinimumPropagator::new(
                propagating_task.start_variable.clone().scaled(1),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect());
            let false_propagator = LessThanMinimumPropagator::new(
                propagating_task.start_variable.clone().scaled(1),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect());
            let _ = LITERAL_TO_PROPAGATORS.lock().unwrap().insert(*literal, true_propagator.clone());
            
            let mut new_propagators = CumulativeLiteral::new(
                ReifiedPropagator::new(
                    true_propagator,
                    *literal),
                ReifiedPropagator::new(
                    false_propagator,
                    literal.not()
                ),
                context.pop_new_propagator_id(),
                context.pop_new_propagator_id(),
            );

            // TODO the init may fail and that is not allowed.
            new_propagators.prop1.initialise_at_root(&mut context.as_initialisation_context(new_propagators.id1)).expect("Prop 1 failed to initialize. As this was not done via root level please do errors via propagation.");
            new_propagators.prop2.initialise_at_root(&mut context.as_initialisation_context(new_propagators.id2)).expect("Prop 2 failed to initialize. As this was not done via root level please do errors via propagation.");
            context.assign_literal(literal, true, explanation)?;

            pumpkin_assert_simple!(context.is_literal_true(literal), "Propagating propagators we just created requires the literal to be set to true");
            context.propagator_id = new_propagators.id1;
            context.with_reification(*literal);
            let result = new_propagators.prop1.propagator.propagate_directly(context);

            context.cumulative_literals.push(new_propagators);

            // Note that the assert may fail if it is equals.
            // I am attributing this to the fact that a profile may appear where at some point an extra unnecessary task overlaps. However, we would still propagate to the end of the profile.
            match result {
                Err(Inconsistency::EmptyDomain) => {return Err(EmptyDomain)}
                Err(_) => {panic!("This propagation function is not allowed to raise a custom conflict.")}
                _ => {}
            }
            
        }  else {
            context.assign_literal(literal, true, explanation)?;
            let map = LITERAL_TO_PROPAGATORS.lock().unwrap();
            let true_propagator = map.get(literal).expect("Since it is not the first time this literal is queried it should have a key in this map");

            pumpkin_assert_simple!(context.is_literal_true(literal), "Propagating propagators with reification requires the literal to be set to true");
            context.with_reification(*literal);
            let result = true_propagator.propagate_directly(context);

            match result {
                Err(Inconsistency::EmptyDomain) => {return Err(EmptyDomain)}
                Err(_) => {panic!("This propagation function is not allowed to raise a conflict. (timetable API does not support it)")}
                _ => {}
            }
        }
        
        context.propagator_id = cur_id;
        context.without_reification();
        pumpkin_assert_simple!(context.lower_bound(&propagating_task.start_variable) >= profile.end + 1, "Propagation did not happen in accordance to the timetable");
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
        // Due to the more optimal propagation strength per profile it can be that we are supposed to skip over other profiles.
        if context.upper_bound(&propagating_task.start_variable) <= profile.start - propagating_task.processing_time {
            continue
        }
        
        let pointwise_timepoint = profile.start
            .max(context.upper_bound(&propagating_task.start_variable));
        
        let mut explanation = create_support(&context.as_readonly(), profile, pointwise_timepoint, underlying_type);
        explanation.add(create_extended_predicate_propagating_task_upper_bound_propagation(context.as_readonly(), propagating_task, profile, Some(pointwise_timepoint), underlying_type));

        let key = MapToLiteral::new(false, global_id, convert_profile_to_raw_ids(profile));
        let mut is_first = false;
        let literal = cache.entry(key).or_insert_with(|| {is_first = true; context.pop_new_literal()});

        // TODO If the literal was set to true then something has gone wrong as we propagate optimally. (delete this assertion in the non optimal case where propagate directly goes to a bound)
        // pumpkin_assert_simple!(!context.is_literal_true(literal), "The literal was already set to true, are your propagators strong enough?");

        let cur_id = context.propagator_id;
        if is_first {
            pumpkin_assert_simple!(!context.is_literal_fixed(literal), "When given a meaning a literal should not have had a value from before");
            literal.make_decidable();
            let true_propagator = LargerOrEqualMinimumPropagator::new(
                propagating_task.start_variable.offset(propagating_task.processing_time).scaled(-1),
                profile.profile_tasks.iter().map(|x| x.start_variable.scaled(-1)).collect());
            let false_propagator = LessThanMinimumPropagator::new(
                propagating_task.start_variable.offset(propagating_task.processing_time).scaled(-1),
                profile.profile_tasks.iter().map(|x| x.start_variable.scaled(-1)).collect());
            let _ = LITERAL_TO_PROPAGATORS.lock().unwrap().insert(*literal, true_propagator.clone());

            let mut new_propagators = CumulativeLiteral::new(
                ReifiedPropagator::new(
                    true_propagator,
                    *literal),
                ReifiedPropagator::new(
                    false_propagator,
                    literal.not()
                ),
                context.pop_new_propagator_id(),
                context.pop_new_propagator_id(),
            );

            // TODO we need to look at these inits. The expect should be removed as it is below.
            new_propagators.prop1.initialise_at_root(&mut context.as_initialisation_context(new_propagators.id1)).expect("Prop 1 failed to initialize. As this was not done via root level please do errors via propagation.");
            new_propagators.prop2.initialise_at_root(&mut context.as_initialisation_context(new_propagators.id2)).expect("Prop 2 failed to initialize. As this was not done via root level please do errors via propagation.");

            context.assign_literal(literal, true, explanation)?;

            pumpkin_assert_simple!(context.is_literal_true(literal), "Propagating propagators we just created requires the literal to be set to true");
            context.propagator_id = new_propagators.id1;
            context.with_reification(*literal);
            let result = new_propagators.prop1.propagator.propagate_directly(context);

            context.cumulative_literals.push(new_propagators);
            
            match result {
                Err(Inconsistency::EmptyDomain) => {return Err(EmptyDomain)}
                Err(_) => {panic!("This propagation function is not allowed to raise a custom conflict.")}
                _ => {}
            }
        } else {
            context.assign_literal(literal, true, explanation)?;
            
            let map = LITERAL_TO_PROPAGATORS.lock().unwrap();
            let true_propagator = map.get(literal).expect("Since it is not the first time this literal is queried it should have a key in this map");

            pumpkin_assert_simple!(context.is_literal_true(literal), "Propagating propagators with reification requires the literal to be set to true");
            context.with_reification(*literal);
            let result = true_propagator.propagate_directly(context);

            match result {
                Err(Inconsistency::EmptyDomain) => {return Err(EmptyDomain)}
                Err(_) => {panic!("This propagation function is not allowed to raise a custom conflict.")}
                _ => {}
            }
        }
        
        context.propagator_id = cur_id;
        context.without_reification();
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