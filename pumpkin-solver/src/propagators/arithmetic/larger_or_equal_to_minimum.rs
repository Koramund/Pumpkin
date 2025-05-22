use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::conjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::domain_events::DomainEvents;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::contexts::{ManipulateStatefulIntegers, StatefulPropagationContext};
use crate::engine::propagation::{EnqueueDecision, PropagationContextMut};
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::LocalId;
use crate::engine::variables::IntegerVariable;

//TODO still need to run this with the highest level of assertions.

/// Bounds-consistent propagator enforcing that [lhs >= min(array)]
#[derive(Clone, Debug)]
pub(crate) struct LargerOrEqualMinimumPropagator<Lhs, Var> {
    lhs: Lhs,
    array: Box<[Var]>,
}

impl<Lhs: IntegerVariable + 'static, Var: IntegerVariable + 'static> LargerOrEqualMinimumPropagator<Lhs, Var> {
    pub(crate) fn new(lhs: Lhs, array: Box<[Var]>, ) -> Self {
        LargerOrEqualMinimumPropagator {
            lhs,
            array,
        }
    }

    pub(crate) fn propagate_directly(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        let restrictor = self.array.iter().min_by_key(|x| context.lower_bound(*x)).unwrap();
        dbg!(self.array.iter().map(|x| context.lower_bound(x)).collect::<Vec<_>>());
        if context.lower_bound(restrictor) > context.lower_bound(&self.lhs) {
            context.set_lower_bound(
                &self.lhs,
                context.lower_bound(restrictor),
                conjunction!([restrictor >= context.lower_bound(restrictor)]))?
        }
        Ok(())
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
        self.propagate_directly(&mut context)
    }

    fn notify(&mut self, mut context: StatefulPropagationContext, local_id: LocalId, event: OpaqueDomainEvent) -> EnqueueDecision {
        EnqueueDecision::Enqueue
    }

    fn priority(&self) -> u32 {
        0
    }

    fn detect_inconsistency(
        &self,
        context: StatefulPropagationContext,
    ) -> Option<PropositionalConjunction> {
        let restrictor = self.array.iter().min_by_key(|x| context.lower_bound(*x)).unwrap();
        if context.lower_bound(restrictor) > context.upper_bound(&self.lhs) {
            Some(conjunction!(
                [restrictor >= context.lower_bound(restrictor)] &
                [self.lhs <= context.upper_bound(&self.lhs)]))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::propagation::EnqueueDecision;
    use crate::engine::test_solver::TestSolver;
    use crate::propagators::arithmetic::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
    use crate::{conjunction, predicate};

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

        solver.assert_bounds(lhs, 3, 3);

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
