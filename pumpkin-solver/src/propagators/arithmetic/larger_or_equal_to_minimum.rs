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

//TODO still need to run this with the highest level of assertions.

/// Bounds-consistent propagator enforcing that [lhs >= min(array)]
#[derive(Clone, Debug)]
pub(crate) struct LargerOrEqualMinimumPropagator<Lhs, Var> {
    lhs: Lhs,
    array: Box<[Var]>,

    /// the current minimum value of the array
    lower_bound_right_hand_side: Box<TrailedInt>,
    /// The most restricting variable.
    restricting_index: Box<TrailedInt>,
}

impl<Lhs: IntegerVariable, Var: IntegerVariable> LargerOrEqualMinimumPropagator<Lhs, Var> {
    pub(crate) fn new(lhs: Lhs, array: Box<[Var]>, ) -> Self {
        LargerOrEqualMinimumPropagator {
            lhs,
            array,
            lower_bound_right_hand_side: Box::from(TrailedInt::default()),
            restricting_index: Box::from(TrailedInt::default())
        }
    }

    fn create_conflict_reason(&self, context: StatefulPropagationContext) -> PropositionalConjunction {
        let restrictor = context.value(*self.restricting_index) as usize;
        conjunction!([self.array[restrictor] >= context.lower_bound(&self.array[restrictor])] & [self.lhs <= context.upper_bound(&self.lhs)])
    }
}

impl<Lhs: IntegerVariable + 'static, Var: IntegerVariable + 'static> Propagator
for LargerOrEqualMinimumPropagator<Lhs, Var>
{
    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        self.array.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::LOWER_BOUND,
                LocalId::from(i as u32),
            );
        });

        let _ = context.register(
            self.lhs.clone(),
            DomainEvents::UPPER_BOUND,
            LocalId::from(self.array.len() as u32),
        );

        let (index, restrictor) = self.array.iter().enumerate().min_by_key(|(_, x)| context.lower_bound(*x)).unwrap().clone();

        self.lower_bound_right_hand_side = Box::from(context.new_stateful_integer(context.lower_bound(restrictor) as i64));
        self.restricting_index = Box::from(context.new_stateful_integer(index as i64));
        
        match self.detect_inconsistency(context.as_stateful_readonly()) {
            None => {Ok(())}
            Some(conflict) => {Err(PropositionalConjunction::from(conflict))}
        }
    }

    fn name(&self) -> &str {
        "GEQtoMin"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        // TODO why does this not have to implement detect_inconsistency?
        let restrictor = self.array.iter().min_by_key(|x| context.lower_bound(*x)).unwrap();
        if context.lower_bound(restrictor) > context.upper_bound(&self.lhs) {
            return Err(Inconsistency::Conflict(conjunction!(
                [restrictor >= context.lower_bound(restrictor)] & 
                [self.lhs <= context.upper_bound(&self.lhs)])));
        }
        
        if context.lower_bound(restrictor) > context.lower_bound(&self.lhs) {
            context.set_lower_bound(
                &self.lhs,
                context.lower_bound(restrictor), 
                conjunction!([restrictor >= context.lower_bound(restrictor)]))?
        }
        Ok(())
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        if let Some(conjunction) = self.detect_inconsistency(context.as_stateful_readonly()) {
            return Err(conjunction.into());
        }
        // The constraint propagated is that the lower bound of LHS is incremented to at least the lower bound of every variable in "array".
        if context.lower_bound(&self.lhs) < context.value(*self.lower_bound_right_hand_side) as i32 {
            let restrictor = context.value(*self.restricting_index) as usize;
            context.set_lower_bound(&self.lhs, context.value(*self.lower_bound_right_hand_side) as i32, conjunction!([self.array[restrictor] >= context.value(*self.lower_bound_right_hand_side) as i32]))?
        }
        Ok(())
    }

    fn notify(&mut self, mut context: StatefulPropagationContext, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision {

        match event.unwrap() {
            // Lower bounds always match to an array node as we don't register to anything else.
            IntDomainEvent::LowerBound => {
                let index = local_id.unpack() as usize;
                
                // The restricting variable was propagated on, see if we can replace it with a restrictor of equal value.
                if index == context.value(*self.restricting_index) as usize {
                    // TODO Get a sorted array somewhere to more easily find alternatives.
                    let (index, restrictor) = self.array.iter().enumerate().min_by_key(|(_, x)| context.lower_bound(*x)).unwrap().clone();

                    // A replacement exists so we move the restrictor around, but we skip enqueueing
                    if context.lower_bound(restrictor) == context.value(*self.lower_bound_right_hand_side) as i32 {

                        context.assign(*self.restricting_index, index as i64);
                        EnqueueDecision::Skip
                    } else {
                        let old_bound = context.value(*self.lower_bound_right_hand_side).clone();
                        let new_bound = context.lower_bound(restrictor) as i64;
                        
                        context.add_assign(*self.lower_bound_right_hand_side, new_bound - old_bound);
                        context.assign(*self.restricting_index, index as i64);
                        EnqueueDecision::Enqueue
                    }
                } else {
                    EnqueueDecision::Skip
                }
            }
            // The upperbound registration only matters for the lhs so we do not have to care about the id.
            IntDomainEvent::UpperBound => {
                // Conflict will arise!
                if context.upper_bound(&self.lhs) < context.value(*self.lower_bound_right_hand_side) as i32 {
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
        if context.upper_bound(&self.lhs) < context.value(*self.lower_bound_right_hand_side) as i32 {
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
    use crate::propagators::arithmetic::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;

    #[test]
    fn basic_test() {
        let mut solver = TestSolver::default();
    
        let a = solver.new_variable(2, 3);
        let b = solver.new_variable(3, 4);
        let c = solver.new_variable(4, 5);
    
        let lhs = solver.new_variable(1, 10);
    
        let _ = solver
            .new_propagator(LargerOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");
    
        solver.assert_bounds(lhs, 2, 10);
    
        let reason = solver.get_reason_int(predicate![lhs >= 2]);
        assert_eq!(conjunction!([a >= 2]), reason);
    }


    #[test]
    fn in_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(3, 3);
        let b = solver.new_variable(3, 4);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 3);

        let _ = solver
            .new_propagator(LargerOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 1, 3);

        let reason = solver.get_reason_int(predicate![lhs >= 3]);
        assert_eq!(conjunction!([a >= 3]), reason);
    }

    #[test]
    fn out_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(4, 5);
        let b = solver.new_variable(4, 5);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 3);

        let _ = solver
            .new_propagator(LargerOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect_err("Solver did not break finding an inconsistent domain");
    }

    #[test]
    fn updating_internal() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 7);
        let b = solver.new_variable(3, 7);
        let c = solver.new_variable(4, 7);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator(LargerOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");
        
        let _ = solver.increase_lower_bound_and_notify(x, 0, a, 4);
        let _ = solver.propagate(x);
        
        dbg!(&solver.reason_store);

        solver.assert_bounds(lhs, 3, 10);

        let reason = solver.get_reason_int(predicate![lhs >= 3]);
        assert_eq!(conjunction!([b >= 3]), reason);
        
    }

    #[test]
    fn test_when_another_restrictor_exists_nothing_happens() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 3);
        let b = solver.new_variable(2, 4);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator(LargerOrEqualMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 2, 10);

        let reason = solver.get_reason_int(predicate![lhs >= 2]);
        assert_eq!(conjunction!([a >= 2]), reason);

        let dec = solver.increase_lower_bound_and_notify(x, 0, a, 3);
        let _ = solver.propagate(x);

        assert_eq!(dec, EnqueueDecision::Skip);
        solver.assert_bounds(lhs, 2, 10);
        assert_eq!(conjunction!([a >= 2]), reason);
    }
}
