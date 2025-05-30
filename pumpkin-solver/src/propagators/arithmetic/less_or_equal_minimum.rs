use crate::basic_types::PropagationStatusCP;
use crate::basic_types::{Inconsistency, PropositionalConjunction};
use crate::{conjunction, predicate};
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::domain_events::DomainEvents;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::contexts::StatefulPropagationContext;
use crate::engine::propagation::{EnqueueDecision, PropagationContextMut};
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::LocalId;
use crate::engine::variables::IntegerVariable;

// TODO still need to run this with the highest level of assertions.
// TODO BEWARE THIS IS A LEQ PROPAGATOR WHILST THE CUMULATIVE RELATION IS AN LE OPERATOR.
// TODO THEREFORE INPUT THE LHS AS AN OFFSET -1, THAT WAY IT BECOMES AN LE RELATION.
// TODO NOTE THAT THIS DOES NOT AFFECT THE LB AS THIS IS AN UB ONLY PROPAGATOR.

/// Bounds-consistent propagator enforcing that [lhs <= min(array)]
#[derive(Clone, Debug)]
pub(crate) struct LessThanMinimumPropagator<Lhs, Var> {
    lhs: Lhs,
    array: Box<[Var]>,
}

impl<Lhs: IntegerVariable, Var: IntegerVariable> LessThanMinimumPropagator<Lhs, Var> {
    pub(crate) fn new(lhs: Lhs, array: Box<[Var]>, ) -> Self {
        LessThanMinimumPropagator {
            lhs,
            array,
        }
    }
}

impl<Lhs: IntegerVariable + 'static, Var: IntegerVariable + 'static> Propagator
for LessThanMinimumPropagator<Lhs, Var>
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
        if let Some(conflict) = self.detect_inconsistency(context.as_stateful_readonly()) {
            return Err(Inconsistency::from(conflict))
        }

        // get the lowest LCT
        let restrictor = self.array.iter().min_by_key(|x| context.upper_bound(*x)).unwrap();
        if context.upper_bound(restrictor) <= context.upper_bound(&self.lhs) {
            context.set_upper_bound(
                &self.lhs,
                context.upper_bound(restrictor) - 1,
                conjunction!([restrictor <= context.upper_bound(restrictor)]))?
        }
        Ok(())
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
        let task_with_earliest_lct = self.array.iter().min_by_key(|x| context.upper_bound(*x)).unwrap();
        if context.lower_bound(&self.lhs) >= context.upper_bound(task_with_earliest_lct)  {
            Some(
                self.array.iter().map(|x| predicate![x <= context.upper_bound(x)]).chain(
                    std::iter::once(predicate![self.lhs >= context.lower_bound(&self.lhs)])).collect()
            )
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::propagation::EnqueueDecision;
    use crate::engine::test_solver::TestSolver;
    use crate::propagators::less_or_equal_minimum::LessThanMinimumPropagator;
    use crate::{conjunction, predicate};

    #[test]
    fn detect_inconsistency_on_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 5);
        let b = solver.new_variable(3, 6);
        let c = solver.new_variable(4, 7);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator_non_fixpoint(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        let _ = solver.increase_lower_bound_and_notify(x, 3, lhs, 1);

        let inconsistency = solver.detect_inconsistency(x);

        assert!(inconsistency.is_some(), "We expected an inconsistency");
    }

    #[test]
    fn detect_inconsistency_off_point() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 5);
        let b = solver.new_variable(3, 5);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 10);

        let x = solver
            .new_propagator_non_fixpoint(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        let _ = solver.decrease_upper_bound_and_notify(x, 3, lhs, 2);

        let inconsistency = solver.detect_inconsistency(x);

        assert!(inconsistency.is_none(), "We expected no inconsistency");
    }

    #[test]
    fn basic_test() {
        let mut solver = TestSolver::default();

        let a = solver.new_variable(2, 3);
        let b = solver.new_variable(3, 4);
        let c = solver.new_variable(4, 5);

        let lhs = solver.new_variable(1, 10);

        let _ = solver
            .new_propagator(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
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
            .new_propagator(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
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
            .new_propagator(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
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
            .new_propagator(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
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
            .new_propagator(LessThanMinimumPropagator::new(lhs, [a, b, c].into()))
            .expect("no empty domain");

        solver.assert_bounds(lhs, 1, 3);

        let reason = solver.get_reason_int(predicate![lhs <= 3]);
        assert_eq!(conjunction!([a <= 3]), reason);
    
        let _ = solver.decrease_upper_bound_and_notify(x, 2, c, 4);
        let _ = solver.propagate(x);
    
        // assert_eq!(dec, EnqueueDecision::Skip);
        solver.assert_bounds(lhs, 1, 3);
        assert_eq!(conjunction!([a <= 3]), reason);
    }
}
