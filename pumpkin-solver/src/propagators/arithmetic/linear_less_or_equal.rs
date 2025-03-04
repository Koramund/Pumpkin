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
use crate::engine::TrailedInt;
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
    // tracks variables that have been activated, aka some lower bound that is not their original lower bound.
    active: Box<[TrailedInt]>,
    multiplicity: usize,
}

impl<Var> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32) -> Self {
        let current_bounds = (0..x.len())
            .map(|_| TrailedInt::default())
            .collect_vec()
            .into();

        let active = (0..x.len())
            .map(|_| TrailedInt::default())
            .collect_vec()
            .into();

        // incremental state will be properly initialized in `Propagator::initialise_at_root`.
        LinearLessOrEqualPropagator::<Var> {
            x,
            c,
            lower_bound_left_hand_side: TrailedInt::default(),
            current_bounds,
            partials: Box::new([]),
            active,
            multiplicity: 1,
        }
    }

    // Basically the explanation is not necessarily optimal. It just marks the current context as wrong.
    // Certain parts of that context may also utilize different lower bounds as wrong conclusions. x >= 2 -> x >= 1.

    // Will need to be altered to more concretely supply a >= n as the reason.
    
    fn create_conflict_reason(&self, context: PropagationContext) -> PropositionalConjunction {
        self.x
            .iter()
            .map(|var| predicate![var >= context.lower_bound(var)])
            .collect()
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
                partial_lowers.push(lower_bound_left_hand_side)
            }

            // updates lower bound according to the default variables
            lower_bound_left_hand_side += context.lower_bound(x_i) as i64;

            // used for internal tracking of the lower bounds of each variable.
            self.current_bounds[i] = context.new_stateful_integer(context.lower_bound(x_i) as i64);
            self.active[i] = context.new_stateful_integer(0);
        });

        // one extra push in case we left one out.
        // TODO this should be removed as we do not reason with the last partial as it can imply nothing.
        if self.x.len() % self.multiplicity != 0 {
            partial_lowers.push(lower_bound_left_hand_side);
        }

        // convert partials_lower into partials by creating new variables via context.create_new_integer_variable
        self.partials = partial_lowers.iter()
            // potentially risky i32 cast.
            .map(|&value| context.create_new_integer_variable(value as i32, self.c))
            .collect_vec()
            .into();

        self.partials.iter().enumerate().for_each(|(i, a_i)| {
            let _ = context.register(a_i.clone(), DomainEvents::BOUNDS, LocalId::from((i + self.x.len()) as u32));
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
        let index = local_id.unpack() as usize;

        // quick return if it is referencing a partial sum as we'll just rely on the raw variables for now.
        if index >= self.x.len() {
            return EnqueueDecision::Enqueue
        };
        let x_i = &self.x[index];

        // local bounds utilized to store old information?
        let old_bound = context.value(self.current_bounds[index]);
        let new_bound = context.lower_bound(x_i) as i64;

        pumpkin_assert_simple!(
            old_bound < new_bound,
            "propagator should only be triggered when lower bounds are tightened, old_bound={old_bound}, new_bound={new_bound}"
        );

        // update active value if a lower bound was updated.
        if context.value(self.active[index]) == 0 {
            context.assign(self.active[index], 1);
        }

        // Utilizes a weird setting way, why not just directly assign?
        // I'm guessing this just sets up the function before propagation. Doing some bookkeeping here.
        // lower_bound is actually what we care about when backtracking for incremental.
        // The others are tracked to properly book-keep on the lower_bound.
        // TODO could also do this for our situation.
        context.add_assign(self.lower_bound_left_hand_side, new_bound - old_bound);
        context.assign(self.current_bounds[index], new_bound);

        EnqueueDecision::Enqueue
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
                        if j >= ((i / self.multiplicity) * self.multiplicity) && j != i && context.value(self.active[j]) > 0 {
                            Some(predicate![x_j >= context.lower_bound(x_j)])
                        } else {
                            None
                        }
                    })
                    .collect();

                match self.partials.get(i / self.multiplicity - 1) {
                    Some(a) => reason.push(predicate!(a >= context.lower_bound(a))),
                    _ => {}
                }

                // then update the variable
                context.set_upper_bound(x_i, bound, reason)?;
            }
        }
        Ok(())
    }
}

impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    /// Updates the partial variables before they are utilized in any explanations.
    fn update_partials(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials.iter().enumerate() {
            let mut partial_bound = self.c;

            for j in 0..self.multiplicity {
                partial_bound = partial_bound - context.lower_bound(&self.x[i * self.multiplicity + j]);
            }

            if partial_bound < context.upper_bound(a_i) {
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
                if i != 0 {
                    reason.push(predicate!(self.partials[i-1] >= context.lower_bound(&self.partials[i-1])));
                }

                context.set_upper_bound(a_i, partial_bound, reason)?;
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
        let x = solver.new_variable(1, 5);
        let y = solver.new_variable(0, 10);

        let propagator = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), 7))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        solver.assert_bounds(x, 1, 5);
        solver.assert_bounds(y, 0, 6);
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
