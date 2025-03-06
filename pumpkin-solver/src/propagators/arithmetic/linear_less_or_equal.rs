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

    // Represents the partial sums.
    partials: Box<[DomainId]>,
    multiplicity: usize,
}

impl<Var> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32) -> Self {
        let multiplicity = 2;

        LinearLessOrEqualPropagator::<Var> {
            x,
            c,
            partials: Box::new([]),
            multiplicity,
        }
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

            // saves the lower bound for the previous three values.
            if (i % self.multiplicity) == 0 && i > 0 {
                partial_lowers.push(lower_bound_left_hand_side);
            }

            // updates lower bound according to the default variables
            lower_bound_left_hand_side += context.lower_bound(x_i) as i64;
        });

        // convert partials_lower into partials by creating new variables via context.create_new_integer_variable
        self.partials = partial_lowers.iter()
            // potentially risky i32 cast.
            .map(|&value| context.create_new_integer_variable(value as i32, self.c))
            .collect_vec()
            .into();

        Ok(())
    }


    // very basic check that verifies we are not in a conflict.
    // Currently only called during "incremental propagation".
    // TODO still need to update this. Do I tho?
    fn detect_inconsistency(
        &self,
        context: StatefulPropagationContext,
    ) -> Option<PropositionalConjunction> {

        let start = (self.x.len() - (((self.x.len() - 1) % self.multiplicity) + 1));
        let end = self.x.len();

        let lb = self.x[start..end]
            .iter()
            .map(|var| context.lower_bound(var))
            .sum() + if self.partials.len() > 0 {context.lower_bound(&self.partials[self.partials.len()-1])} else {0};

        if lb > self.c {
            let mut reason: PropositionalConjunction = self.x[start..end]
                .iter()
                .map(|var| predicate![var >= context.lower_bound(var)])
                .collect();
            if self.partials.len() > 0 {
                reason.add(predicate!(self.partials[self.partials.len()-1] >= context.lower_bound(&self.partials[self.partials.len()-1])));
                dbg!(&self.partials[self.partials.len()-1]);
            }
            dbg!(&reason);
            Some(reason)
        } else {
            None
        }
    }

    fn priority(&self) -> u32 {
        0
    }

    fn name(&self) -> &str {
        "LinearLeq"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        // So there is indeed a scenario where the lower bounds may overflow the i32.
        // That is an issue that will not be resolved for now.
        // let lower_bound_left_hand_side = self
        //     .x
        //     .iter()
        //     .map(|var| context.lower_bound(var) as i64)
        //     .sum::<i64>();


        self.maintain_upper_bound_consistency(&mut context)?;
        self.update_bounds(context)?;

        Ok(())
    }
}

impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    // This function is responsible of setting the upperbounds of the partials
    /// This is responsible for setting a <= n.
    fn maintain_upper_bound_consistency(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // // TODO this only takes care of UB of a into its surrounds.
        // // TODO it does not take care of updating the upperbound of a because of its surroundings.
        //
        // // updating upperbounds of a due to variations in its surrounding requires a left to right procedure.

        // Too lazy to do it properly for now but there is of course no last partial to update if there are no partials.
        if self.partials.len() > 0 {
            let start = (self.x.len() - (((self.x.len() - 1) % self.multiplicity) + 1));
            let end = self.x.len();

            let new_ub = self.c - self.x[start..end].iter().map(|value| {context.lower_bound(value)}).reduce(|a, b| a + b).unwrap();
            if new_ub < context.upper_bound(&self.partials[self.partials.len()-1]) {
                let last_partial_reason: PropositionalConjunction = self.x[start..end].iter().map(|value| {predicate!(value >= context.lower_bound(value))}).collect();
                context.set_upper_bound(&self.partials[self.partials.len()-1], new_ub, last_partial_reason)?;
            }
        }

        // update the upperbounds of all the other a variables.
        // it loops over a_i but ever loop updates a_i - 1
        self.partials.iter().enumerate().rev().for_each(|(i, a_i)| {
            let new_ub_for_prev_a = context.upper_bound(a_i) - self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().map(|value| context.lower_bound(value)).reduce(|acc, value| acc + value).unwrap();
            // first update the previous a value.
            if i > 0 && new_ub_for_prev_a < context.upper_bound(&self.partials[i - 1]) {
                let mut reason: PropositionalConjunction = self.x[i * self.multiplicity..(i + 1) * self.multiplicity].iter().map(|value| predicate!(value >= context.lower_bound(value))).collect();
                reason.add(predicate!(a_i <= context.upper_bound(a_i)));

                context.set_upper_bound(&self.partials[i - 1], new_ub_for_prev_a, reason)?;
            }
        });

        Ok(())
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
    /// Responsible for setting x_i <= n
    fn update_bounds(&self, mut context: PropagationContextMut) -> PropagationStatusCP {
        self.update_partials(&mut context)?;

        for (i, x_i) in self.x.iter().enumerate() {
            // The lower bound should be calculated locally.
            // The upperbound is defined by c - the lower bound of the previous partial and its neighbours.
            // This means the first variables only have each other for the lower bounds.

            let start = (i / self.multiplicity) * self.multiplicity;
            let end = min(start + self.multiplicity, self.x.len());

            let surrounding_consumption = self.x[start..end].iter().map(|x_j| {context.lower_bound(&x_j)}).sum() - context.lower_bound(&x_i) + if (i >= self.multiplicity) {context.lower_bound(&self.partials[i/ self.multiplicity-1])} else {0};

            // The remaining energy is determined by the next partials upper bound as that explains how much energy has been consumed ahead.
            let upperbound = if (i/self.multiplicity < self.partials.len()) {context.upper_bound(&self.partials[i/self.multiplicity])} else {self.c};
            let bound = upperbound - surrounding_consumption;

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.upper_bound(x_i) > bound {
                // reason is now defined as the partial + any activated literal not in one of those partials
                let mut reason: PropositionalConjunction = self
                    .x
                    .iter()
                    .enumerate()
                    .filter_map(|(j, x_j)| {
                        // incredibly waste full but enumerate loses the index when we do it any other way.
                        if j >= start && j != i && j < end {
                            Some(predicate![x_j >= context.lower_bound(x_j)])
                        } else {
                            None
                        }
                    })
                    .collect();

                // lower bound of previous partial is required as it determines energy consumption
                if i >= self.multiplicity {
                    let a = &self.partials[(i / self.multiplicity) - 1];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }

                // Upper bound of next partial is required as it determines energy capacity
                if i / self.multiplicity < self.partials.len() {
                    let a = &self.partials[i / self.multiplicity];
                    reason.push(predicate!(a <= context.lower_bound(a)))
                }

                // then update the variable
                context.set_upper_bound(x_i, bound, reason)?;
            }
        }
        Ok(())
    }

    // In order to propagate the upperbounds of our x's we need to propagate on the lower bound of our a's
    // We simply move from left to right, detecting the lower bound of a
    // And then propagating it.
    /// This is responsible for setting a >= n.
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
                dbg!((i, partial_bound, context.lower_bound(a_i)));
                // update value of the partial.

                let start = i * self.multiplicity;
                let end = min(start + self.multiplicity, self.x.len());

                // First take the relevant section as the reason.
                let mut reason: PropositionalConjunction = self.x[start..end]
                    .iter()
                    .map(|x_i| {
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
