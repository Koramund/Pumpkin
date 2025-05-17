use std::collections::HashMap;
use std::ops::Not;
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};
use crate::basic_types::cumulative_literal::{CumulativeLiteral, MapToLiteral};
use crate::basic_types::PropositionalConjunction;
use crate::engine::EmptyDomain;
use crate::engine::propagation::{PropagationContext, PropagationContextMut, ReadDomains};
use crate::predicates::Predicate;
use crate::propagators::{ReifiedPropagator, ResourceProfile, Task};
use crate::{pumpkin_assert_eq_simple, pumpkin_assert_simple};
use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessOrEqualMinimumPropagator;
use crate::variables::{IntegerVariable, Literal};


pub static CUMULATIVE_TO_LITERAL: LazyLock<Mutex<HashMap<MapToLiteral, Literal>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(crate) fn propagate_lower_bounds_with_extended_explanations<Var: IntegerVariable + 'static>(
    context: &mut PropagationContextMut,
    profiles: &[&ResourceProfile<Var>],
    propagating_task: &Rc<Task<Var>>,
) -> Result<(), EmptyDomain> {
    let global_id = propagating_task.start_variable.get_id();
    let mut cache = CUMULATIVE_TO_LITERAL.lock().unwrap();

    for profile in profiles {
        let explanation = create_support(&context.as_readonly(), profile);

        let key = MapToLiteral::new(true, global_id, convert_profile_to_raw_ids(profile));
        let literal = cache.entry(key).or_insert(context.create_new_literal(None));

        pumpkin_assert_simple!(context.lower_bound(literal) >= 0, "We are about to set this literal to true so there is no way it can currently be false.");
        context.assign_literal(literal, true, explanation)?;
        
        // Start >= min(end of conflicts)
        
        // let new_propagators = CumulativeLiteral::new(
        //     ReifiedPropagator::new(
        //         LargerOrEqualMinimumPropagator::new(
        //             propagating_task.start_variable.clone(),
        //             profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect()),
        //         *literal),
        //     
        // )
        // let prop1 = 
            
        
        // This models the opposite case making sure that the reification literal is also set to false whenever possible.
        let prop2 = ReifiedPropagator::new(
            LessOrEqualMinimumPropagator::new(
                propagating_task.start_variable.clone(),
                profile.profile_tasks.iter().map(|x| x.start_variable.offset(x.processing_time)).collect()),
            literal.not()
        );
        
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
/// Note that this function is agnostic to lower and upper bound variations
/// Therefore after calling this function one should add their lower/upper bound predicate for the shiting task.
fn create_support<Var: IntegerVariable + 'static>(
    context: &PropagationContext,
    profile: &ResourceProfile<Var>,
) -> PropositionalConjunction {

    PropositionalConjunction::default()
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
/// [`CumulativeExplanationType::extended`])
pub(crate) fn create_extended_conflict_explanation<Var: IntegerVariable + 'static>(
    conflict_profile: &ResourceProfile<Var>,
) -> PropositionalConjunction {
    PropositionalConjunction::default()
}

pub(crate) fn create_extended_predicate_propagating_task_lower_bound_propagation<Var>(
    task: &Rc<Task<Var>>,
    time_point: Option<i32>,
) -> Predicate
where
    Var: IntegerVariable + 'static,
{
    // TODO predicate should be the updating of the reification literal?
}

pub(crate) fn create_extended_predicate_propagating_task_upper_bound_propagation<Var>(
    task: &Rc<Task<Var>>,
    time_point: Option<i32>,
) -> Predicate
where
    Var: IntegerVariable + 'static,
{
    // TODO predicate should be the updating of the reification literal?
}