use crate::basic_types::{Inconsistency, PropositionalConjunction};
use crate::basic_types::PropagationStatusCP;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::domain_events::DomainEvents;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::contexts::{ManipulateStatefulIntegers, StatefulPropagationContext};
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{EnqueueDecision, LocalId};
use crate::engine::variables::IntegerVariable;
use crate::engine::{IntDomainEvent, TrailedInt};
use crate::conjunction;

// TODO still need to run this with the highest level of assertions.
// TODO BEWARE THIS IS A LEQ PROPAGATOR WHILST THE CUMULATIVE RELATION IS AN LE OPERATOR.
// TODO THEREFORE INPUT THE LHS AS AN OFFSET -1, THAT WAY IT BECOMES AN LE RELATION.
// TODO NOTE THAT THIS DOES NOT AFFECT THE LB AS THIS IS AN UB ONLY PROPAGATOR.

/// Bounds-consistent propagator enforcing that [lhs <= min(array)]
#[derive(Clone, Debug)]
pub(crate) struct LessOrEqualMinimumPropagator<Lhs, Var> {
    lhs: Lhs,
    array: Box<[Var]>,

    /// the current minimum value of the array
    upper_bound_right_hand_side: Box<TrailedInt>,
    /// The most restricting variable.
    restricting_index: Box<TrailedInt>,
}

impl<Lhs: IntegerVariable, Var: IntegerVariable> LessOrEqualMinimumPropagator<Lhs, Var> {
    pub(crate) fn new(lhs: Lhs, array: Box<[Var]>, ) -> Self {
        LessOrEqualMinimumPropagator {
            lhs,
            array,
            upper_bound_right_hand_side: Box::from(TrailedInt::default()),
            restricting_index: Box::from(TrailedInt::default())
        }
    }

    fn create_conflict_reason(&self, context: StatefulPropagationContext) -> PropositionalConjunction {
        let restrictor = context.value(*self.restricting_index) as usize;
        conjunction!([self.array[restrictor] <= context.upper_bound(&self.array[restrictor])] & [self.lhs >= context.lower_bound(&self.lhs)])
    }
}

impl<Lhs: IntegerVariable + 'static, Var: IntegerVariable + 'static> Propagator
for LessOrEqualMinimumPropagator<Lhs, Var>
{
    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        self.array.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::UPPER_BOUND,
                LocalId::from(i as u32),
            );
        });

        let _ = context.register(
            self.lhs.clone(),
            DomainEvents::LOWER_BOUND,
            LocalId::from(self.array.len() as u32),
        );

        let (index, restrictor) = self.array.iter().enumerate().min_by_key(|(_, x)| context.upper_bound(*x)).unwrap().clone();

        self.upper_bound_right_hand_side = Box::from(context.new_stateful_integer(context.upper_bound(restrictor) as i64));
        self.restricting_index = Box::from(context.new_stateful_integer(index as i64));

        match self.detect_inconsistency(context.as_stateful_readonly()) {
            None => {Ok(())}
            Some(conflict) => {Err(PropositionalConjunction::from(conflict))}
        }
    }

    fn name(&self) -> &str {
        "LEQtoMin"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        let restrictor = self.array.iter().min_by_key(|x| context.upper_bound(*x)).unwrap();
        if context.upper_bound(restrictor) < context.lower_bound(&self.lhs) {
            return Err(Inconsistency::Conflict(conjunction!(
                [restrictor <= context.upper_bound(restrictor)] &
                [self.lhs >= context.lower_bound(&self.lhs)])));
        }

        if context.upper_bound(restrictor) < context.upper_bound(&self.lhs) {
            context.set_upper_bound(
                &self.lhs,
                context.upper_bound(restrictor),
                conjunction!([restrictor <= context.upper_bound(restrictor)]))?
        }
        Ok(())
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        if let Some(conjunction) = self.detect_inconsistency(context.as_stateful_readonly()) {
            return Err(conjunction.into());
        }
        // The constraint propagated is that the lower bound of LHS is incremented to at least the lower bound of every variable in "array".
        if context.upper_bound(&self.lhs) > context.value(*self.upper_bound_right_hand_side) as i32 {
            let restrictor = context.value(*self.restricting_index) as usize;
            context.set_upper_bound(&self.lhs, context.value(*self.upper_bound_right_hand_side) as i32, conjunction!([self.array[restrictor] <= context.value(*self.upper_bound_right_hand_side) as i32]))?
        }
        Ok(())
    }

    fn notify(&mut self, mut context: StatefulPropagationContext, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision {

        match event.unwrap() {
            // Lower bounds always match to an array node as we don't register to anything else.
            IntDomainEvent::UpperBound => {
                let index = local_id.unpack() as usize;

                // If the restrictor updated we instantly enqueue
                if index == context.value(*self.restricting_index) as usize {
                    context.add_assign(*self.upper_bound_right_hand_side, context.upper_bound(&self.array[index]) as i64 - context.value(*self.upper_bound_right_hand_side));
                    return EnqueueDecision::Enqueue
                }
                
                let new_candidate = &self.array[index];
                
                let old_bound = context.value(*self.upper_bound_right_hand_side);
                let new_bound = context.upper_bound(new_candidate) as i64;
                
                // Otherwise it depends on if this new candidate tightens the bound or not.
                if new_bound < old_bound {
                    context.add_assign(*self.upper_bound_right_hand_side, new_bound - old_bound);
                    context.assign(*self.restricting_index, index as i64);
                    // Update internals and enqueue
                    EnqueueDecision::Enqueue
                } else {
                    EnqueueDecision::Skip
                }
            }
            // The upperbound registration only matters for the lhs so we do not have to care about the id.
            IntDomainEvent::LowerBound => {
                // Conflict will arise!
                if context.lower_bound(&self.lhs) > context.value(*self.upper_bound_right_hand_side) as i32 {
                    EnqueueDecision::Enqueue
                } else {
                    // But otherwise nothing matters
                    EnqueueDecision::Skip
                }
            }
            _ => {EnqueueDecision::Enqueue}
        }
    }

    fn priority(&self) -> u32 {
        0
    }

    fn detect_inconsistency(
        &self,
        context: StatefulPropagationContext,
    ) -> Option<PropositionalConjunction> {
        if context.lower_bound(&self.lhs) > context.value(*self.upper_bound_right_hand_side) as i32 {
            Some(self.create_conflict_reason(context))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::test_solver::TestSolver;
    use crate::{conjunction, predicate};
    use crate::engine::propagation::EnqueueDecision;
    use crate::propagators::less_or_equal_minimum::LessOrEqualMinimumPropagator;

    #[test]
    fn basic_test() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 3);
        let b = solver.new_variable(3, 4);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 10);

        let _ = solver
            .new_propagator(LessOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 1, 3);

        let reason = solver.get_reason_int(predicate![lhs <= 3]);
        assert_eq!(conjunction!([a <= 3]), reason);
    }


    #[test]
    fn in_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 5);
        let b = solver.new_variable(1, 3);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(3, 6);

        let _ = solver
            .new_propagator(LessOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 3, 3);

        let reason = solver.get_reason_int(predicate![lhs <= 3]);
        assert_eq!(conjunction!([b <= 3]), reason);
    }

    #[test]
    fn out_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(4, 5);
        let b = solver.new_variable(4, 5);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(6, 10);

        let _ = solver
            .new_propagator(LessOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect_err("Solver did not break finding an inconsistent domain");
    }

    #[test]
    fn updating_internal() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 7);
        let b = solver.new_variable(3, 8);
        let c = solver.new_variable(4, 9);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator(LessOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        let dec = solver.decrease_upper_bound_and_notify(x, 0, a, 5);
        let _ = solver.propagate(x);

        dbg!(&solver.reason_store);
        assert_eq!(dec, EnqueueDecision::Enqueue);
        solver.assert_bounds(lhs, 1, 5);

        let reason = solver.get_reason_int(predicate![lhs <= 5]);
        assert_eq!(conjunction!([a <= 5]), reason);

    }

    #[test]
    fn test_when_another_unrelated_variable_nothing_happens() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 3);
        let b = solver.new_variable(3, 4);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator(LessOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 1, 3);

        let reason = solver.get_reason_int(predicate![lhs <= 3]);
        assert_eq!(conjunction!([a <= 3]), reason);
    
        let dec = solver.decrease_upper_bound_and_notify(x, 2, c, 4);
        let _ = solver.propagate(x);
    
        assert_eq!(dec, EnqueueDecision::Skip);
        solver.assert_bounds(lhs, 1, 3);
        assert_eq!(conjunction!([a <= 3]), reason);
    }
}
