use std::cmp::min;
use itertools::Itertools;

use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::domain_events::DomainEvents;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::contexts::ManipulateStatefulIntegers;
use crate::engine::propagation::contexts::StatefulPropagationContext;
use crate::engine::propagation::EnqueueDecision;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContext;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::variables::IntegerVariable;
use crate::engine::{IntDomainEvent, TrailedInt};
use crate::predicate;
use crate::pumpkin_assert_simple;
use crate::variables::DomainId;

/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagator<Var> {
    x: Box<[Var]>,
    c: i32,

    /// The lower bound of the sum of the left-hand side. This is incremental state.
    lower_bound_left_hand_side: TrailedInt,
    /// The value at index `i` is the bound for `x[i]`.
    current_bounds: Box<[TrailedInt]>,
    // Represents the partial sums.
    partials: Box<[DomainId]>,
    // The value at index `i` is the bound for `a[i]`
    current_partial_bounds: Box<[TrailedInt]>,
    multiplicity: usize,
}

impl<Var> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32) -> Self {
        let multiplicity = 2;
        let current_bounds = (0..x.len())
            .map(|_| TrailedInt::default())
            .collect_vec()
            .into();

        let current_partial_bounds;
        if x.len() % multiplicity != 0 {
            current_partial_bounds = (0..x.len() / multiplicity)
                .map(|_| TrailedInt::default())
                .collect_vec()
                .into();
        } else {
            current_partial_bounds = (0..(x.len() / multiplicity) - 1)
                .map(|_| TrailedInt::default())
                .collect_vec()
                .into();
        };

        // incremental state will be properly initialized in `Propagator::initialise_at_root`.
        LinearLessOrEqualPropagator::<Var> {
            x,
            c,
            lower_bound_left_hand_side: TrailedInt::default(),
            current_bounds,
            partials: Box::new([]),
            current_partial_bounds,
            multiplicity,
        }
    }

    // Basically the explanation is not necessarily optimal. It just marks the current context as wrong.
    // Certain parts of that context may also utilize different lower bounds as wrong conclusions. x >= 2 -> x >= 1.

    // Will need to be altered to more concretely supply a >= n as the reason.

    // Isn't the true conflict reason (apart from variables with empty domains)
    // That the last partial and the last variables have overshot their domain?
    fn create_conflict_reason(&self, context: PropagationContext) -> PropositionalConjunction {
        let start = (self.x.len() - (((self.x.len() - 1) % self.multiplicity) + 1));
        let end = self.x.len();

        let mut reason: PropositionalConjunction = self.x[start..end]
            .iter()
            .map(|var| predicate![var >= context.lower_bound(var)])
            .collect();
        reason.add(predicate!(self.partials[self.partials.len()-1] >= context.lower_bound(&self.partials[self.partials.len()-1])));
        reason
    }
}

impl<Var: 'static> Propagator for LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    // This function needs to be altered to create a series of variables a_i
    fn initialise_at_root(&mut self, context: &mut PropagatorInitialisationContext, ) -> Result<(), PropositionalConjunction> {
        let mut lower_bound_left_hand_side = 0_i64;
        // this registers the propagator to be notified of domain changes

        let mut partial_lowers: Vec<i64> = Vec::new();

        self.x.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::LOWER_BOUND,
                LocalId::from(i as u32),
            );

            // saves the lower bound for the previous three values.
            if (i % self.multiplicity) == 0 && i > 0 {
                partial_lowers.push(lower_bound_left_hand_side);
            }

            // updates lower bound according to the default variables
            lower_bound_left_hand_side += context.lower_bound(x_i) as i64;

            // used for internal tracking of the lower bounds of each variable.
            self.current_bounds[i] = context.new_stateful_integer(context.lower_bound(x_i) as i64);
        });

        // convert partials_lower into partials by creating new variables via context.create_new_integer_variable
        self.partials = partial_lowers.iter()
            // potentially risky i32 cast.
            .map(|&value| context.create_new_integer_variable(value as i32, self.c))
            .collect_vec()
            .into();

        // init partial bounds for incrementality
        partial_lowers.iter().enumerate().for_each(|(i, &value)| {
            self.current_partial_bounds[i] = context.new_stateful_integer(value);
        });

        self.partials.iter().enumerate().for_each(|(i, a_i)| {
            let _ = context.register(a_i.clone(), DomainEvents::LOWER_BOUND, LocalId::from((i + self.x.len()) as u32));
        });


        // Represents the sum of the x_i sums.
        self.lower_bound_left_hand_side = context.new_stateful_integer(lower_bound_left_hand_side);

        if let Some(conjunction) = self.detect_inconsistency(context.as_stateful_readonly()) {
            Err(conjunction)
        } else {
            Ok(())
        }
    }

    // very basic check that verifies we are not in a conflict.
    // Currently only called during "incremental propagation".
    // TODO still need to update this. Do I tho?
    fn detect_inconsistency(
        &self,
        context: StatefulPropagationContext,
    ) -> Option<PropositionalConjunction> {
        if (self.c as i64) < context.value(self.lower_bound_left_hand_side) {
            Some(self.create_conflict_reason(context.as_readonly()))
        } else {
            None
        }
    }

    fn notify(
        &mut self,
        mut context: StatefulPropagationContext,
        local_id: LocalId,
        _event: OpaqueDomainEvent,
    ) -> EnqueueDecision {


        match _event.unwrap() {
            IntDomainEvent::LowerBound => {
                self.maintain_lower_bound_incrementality(context, local_id)
            }
            _ => {EnqueueDecision::Enqueue}
        }

    }

    fn priority(&self) -> u32 {
        0
    }

    fn name(&self) -> &str {
        "LinearLeq"
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        if let Some(conjunction) = self.detect_inconsistency(context.as_stateful_readonly()) {
            return Err(conjunction.into());
        }

        let lower_bound_left_hand_side =
            match TryInto::<i32>::try_into(context.value(self.lower_bound_left_hand_side)) {
                Ok(bound) => bound,
                Err(_) if context.value(self.lower_bound_left_hand_side).is_positive() => {
                    // We cannot fit the `lower_bound_left_hand_side` into an i32 due to an
                    // overflow (hence the check that the lower-bound on the left-hand side is
                    // positive)
                    //
                    // This means that the lower-bounds of the current variables will always be
                    // higher than the right-hand side (with a maximum value of i32). We thus
                    // return a conflict
                    return Err(self.create_conflict_reason(context.as_readonly()).into());
                }
                Err(_) => {
                    // We cannot fit the `lower_bound_left_hand_side` into an i32 due to an
                    // underflow
                    //
                    // This means that the constraint is always satisfied
                    return Ok(());
                }
            };

        self.maintain_upper_bound_consistency(&mut context);
        
        self.update_bounds(context, lower_bound_left_hand_side)?;

        Ok(())
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        let lower_bound_left_hand_side = self
            .x
            .iter()
            .map(|var| context.lower_bound(var) as i64)
            .sum::<i64>();

        let lower_bound_left_hand_side = match TryInto::<i32>::try_into(lower_bound_left_hand_side)
        {
            Ok(bound) => bound,
            Err(_) if context.value(self.lower_bound_left_hand_side).is_positive() => {
                // We cannot fit the `lower_bound_left_hand_side` into an i32 due to an
                // overflow (hence the check that the lower-bound on the left-hand side is
                // positive)
                //
                // This means that the lower-bounds of the current variables will always be
                // higher than the right-hand side (with a maximum value of i32). We thus
                // return a conflict
                return Err(self.create_conflict_reason(context.as_readonly()).into());
            }
            Err(_) => {
                // We cannot fit the `lower_bound_left_hand_side` into an i32 due to an
                // underflow
                //
                // This means that the constraint is always satisfied
                return Ok(());
            }
        };

        self.update_bounds(context, lower_bound_left_hand_side)?;

        Ok(())
    }
}

impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    fn maintain_upper_bound_consistency(&mut self, mut context: &mut PropagationContextMut) {
        // // TODO this only takes care of UB of a into its surrounds.
        // // TODO it does not take care of updating the upperbound of a because of its surroundings.
        //
        // // updating upperbounds of a due to variations in its surrounding requires a left to right procedure.
        // self.partials.iter().enumerate().for_each(|(i, a_i)| {
        //
        //     let new_ub: i32 = self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().map(|x| context.upper_bound(x) as i32).sum();
        //
        //
        //
        // });


        // Too lazy to do it properly for now but there is of course no last partial to update if there are no partials.
        if self.partials.len() > 0 {
            let start = (self.x.len() - (((self.x.len() - 1) % self.multiplicity) + 1));
            let end = self.x.len();

            let new_ub = self.c - self.x[start..end].iter().map(|value| {context.lower_bound(value)}).reduce(|a, b| a + b).unwrap();
            if new_ub < context.upper_bound(&self.partials[self.partials.len()-1]) {
                let last_partial_reason: PropositionalConjunction = self.x[start..end].iter().map(|value| {predicate!(value >= context.lower_bound(value))}).collect();
                context.set_upper_bound(&self.partials[self.partials.len()-1], new_ub, last_partial_reason).expect("failed to set upper bound value for the last partial");
            }
        }



        self.partials.iter().enumerate().rev().for_each(|(i, a_i)| {
            let new_ub_for_prev_a = context.upper_bound(a_i) - self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().map(|value| context.lower_bound(value)).reduce(|acc, value| acc + value).unwrap();
            // first update the previous a value.
            if i > 0 && new_ub_for_prev_a < context.upper_bound(&self.partials[i - 1]) {
                let mut reason: PropositionalConjunction = self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().map(|value| predicate!(value >= context.lower_bound(value))).collect();
                reason.add(predicate!(a_i <= context.upper_bound(a_i)));

                context.set_upper_bound(&self.partials[i - 1], new_ub_for_prev_a, reason).expect("setting of upperbound for the previous a_i failed");
            }

            // Then update all the x below
            self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().enumerate().for_each(|(i_x, x_i)| {

                let mut new_ub_for_x_i: i32 = context.upper_bound(a_i) -
                    self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().enumerate().filter_map(|(j, x_j)| {
                        if i_x != j { Some(context.lower_bound(x_j)) } else { None }
                    }).reduce(|acc, value| acc + value).unwrap();;
                let prev_a: &DomainId;
                let safe_flag = i > 0;
                if safe_flag {
                    prev_a = &self.partials[i - 1];
                    new_ub_for_x_i = new_ub_for_x_i - context.lower_bound(prev_a);
                } else {
                    // inits prev_a with some default that will not be used again.
                    prev_a = &self.partials[0];
                }

                if new_ub_for_x_i < context.upper_bound(x_i) {
                    let mut reason: PropositionalConjunction = self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().enumerate().filter_map(|(j, x_j)| {
                        if i_x != j { Some(predicate!(x_j >= context.lower_bound(x_j))) } else { None }
                    }).collect();
                    reason.add(predicate!(a_i <= context.upper_bound(a_i)));
                    if safe_flag {reason.add(predicate!(prev_a >= context.lower_bound(prev_a)));}
                    

                    context.set_upper_bound(x_i, new_ub_for_x_i, reason).expect("setting of upperbound for an x_i failed.");
                }
            })
        });
    }
}

impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    fn maintain_lower_bound_incrementality(&mut self, mut context: StatefulPropagationContext, local_id: LocalId) -> EnqueueDecision {
        let index = local_id.unpack() as usize;

        let partial_index: usize;
        let diff: i64;

        if index >= self.x.len() {
            // scenario where only a partial is updated
            partial_index = index - self.x.len();
            diff = context.lower_bound(&self.partials[partial_index]) as i64 - context.value(self.current_partial_bounds[partial_index]);
            let siz = self.x.len();
            let old = context.value(self.current_partial_bounds[partial_index]);
            let new = context.lower_bound(&self.partials[partial_index]) as i64;

            if diff == 0 {return EnqueueDecision::Skip}
            
            pumpkin_assert_simple!(
                diff > 0,
                "propagator should only trigger if lower bounds are tightened yet a diff of {diff} was found. Index: {index}, partial: {partial_index}, instance_size: {siz}, old: {old}, new: {new}",
            );
        } else {
            // scenario where an x is updated.
            partial_index = index / self.multiplicity;
            diff = context.lower_bound(&self.x[index]) as i64 - context.value(self.current_bounds[index]);

            context.assign(self.current_bounds[index], context.lower_bound(&self.x[index]) as i64);
        }

        // TODO this fails.
        let siz = self.x.len();

        pumpkin_assert_simple!(
                diff > 0,
                "propagator should only trigger if lower bounds are tightened yet a diff of {diff} was found. Index: {index}, partial: {partial_index}, instance_size: {siz}",
            );


        // TODO test if this scenario occurs because it might happen that once update_partials starts reasoning that suddenly a lot of notification might start piling on.
        // if diff == 0 {return EnqueueDecision::Skip}

        // scenario for an a variable
        // TODO note this method only keeps track of our incremental datas tructure without justifying the partials sums in their explanations yet.
        // That happens in the propagate function
        // TODO That still needs to happen in the propagate function by utilizing this datastructure. It is currently recalculating it anyways every time.

        // we thus update every partial with this difference.
        // Note that partial_index == self.current_partial_bounds.len() is a possibility. If Rust is nice it will just skip the loop then.

        for i in partial_index..self.current_partial_bounds.len() {
            context.add_assign(self.current_partial_bounds[i], diff);
        }


        // finally we update the LHS
        context.add_assign(self.lower_bound_left_hand_side, diff);

        EnqueueDecision::Enqueue
    }
}

impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    // now comes the tricky part. Updating the bounds in such a way that we rely on the partials.
    // the best way is to probably just track which variables have already been activated.
    // If any variable is assigned it is explained by the values in its partial and the previous partial.
    // If a variable to the right has been activated it will also be used in this conjunction.
    // This way we can still get the partials in there if the order is violated.
    /// Updates the bounds of all the variables `x`
    /// Note that it calls update_partials to ensure consistency before propagating.
    fn update_bounds(&self, mut context: PropagationContextMut, lower_bound_left_hand_side: i32) -> PropagationStatusCP {
        self.update_partials(&mut context)?;

        for (i, x_i) in self.x.iter().enumerate() {
            let bound = self.c - (lower_bound_left_hand_side - context.lower_bound(x_i));

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.upper_bound(x_i) > bound {
                // reason is now defined as the partial + any activated literal not in one of those partials
                let mut reason: PropositionalConjunction = self
                    .x
                    .iter()
                    .enumerate()
                    .filter_map(|(j, x_j)| {
                        // using integer division to denote the bounds.
                        if j >= ((i / self.multiplicity) * self.multiplicity) && j != i {
                            Some(predicate![x_j >= context.lower_bound(x_j)])
                        } else {
                            None
                        }
                    })
                    .collect();

                if i >= self.multiplicity {
                    let a = &self.partials[(i / self.multiplicity) - 1];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }

                // then update the variable
                context.set_upper_bound(x_i, bound, reason)?;
            }
        }
        Ok(())
    }

    fn update_partials(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials.iter().enumerate() {
            let mut partial_bound: i32 = 0;

            for j in 0..self.multiplicity {
                partial_bound = partial_bound + context.lower_bound(&self.x[i * self.multiplicity + j]);
            }
            if i > 0 {
                partial_bound = partial_bound + context.lower_bound(&self.partials[i - 1]);
            }

            if partial_bound > context.lower_bound(a_i) {
                // update value of the partial.

                let start = i * self.multiplicity;
                let end = min(start + self.multiplicity, self.x.len());

                // First take the relevant section as the reason.
                let mut reason: PropositionalConjunction = self.x[start..end]
                    .iter()
                    .enumerate().map(|(_, x_i)| {
                    predicate!(x_i >= context.lower_bound(x_i))
                }).collect();

                // if there is a partial then add it as well.
                // may be more optimal to utilize .get and matching no clue how the compiler deals with that.
                if i > 0 {
                    reason.push(predicate!(self.partials[i-1] >= context.lower_bound(&self.partials[i-1])));
                }

                context.set_lower_bound(a_i, partial_bound, reason)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conjunction;
    use crate::engine::test_solver::TestSolver;

    #[test]
    fn test_bounds_are_propagated() {
        let mut solver = TestSolver::default();
        let z = solver.new_variable(2, 8);
        let z1 = solver.new_variable(0, 7);
        let x2 = solver.new_variable(2, 5);
        let x = solver.new_variable(1, 5);
        let y = solver.new_variable(0, 10);
        let p = solver.new_variable(1, 5);

        let propagator = solver
            .new_propagator(LinearLessOrEqualPropagator::new([z,z1, x2, x, y, p].into(), 12))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");
        
        solver.increase_lower_bound_and_notify(propagator, 1, z1, 2);

        solver.propagate(propagator).expect("non-empty domain");

        println!("{}", solver.get_reason_int(predicate!(y <= 6)));

        println!("{:?}", solver.reason_store);
        solver.assert_bounds(z, 2, 6);
        solver.assert_bounds(z1, 2, 6);
        solver.assert_bounds(x2, 2, 5);
        solver.assert_bounds(x, 1, 5);
        solver.assert_bounds(y, 0, 4);
        solver.assert_bounds(p, 1, 5);

        solver.decrease_upper_bound_and_notify(propagator, 1, z, 2);
    }

    #[test]
    fn test_explanations() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(1, 5);
        let y = solver.new_variable(0, 10);

        let propagator = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), 7))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        let reason = solver.get_reason_int(predicate![y <= 6]);
        
        assert_eq!(conjunction!([x >= 1]), reason);
    }

    #[test]
    fn overflow_leads_to_conflict() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MAX, i32::MAX);
        let y = solver.new_variable(1, 1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), i32::MAX))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), i32::MIN))
            .expect("Expected no error to be detected");
    }
}
