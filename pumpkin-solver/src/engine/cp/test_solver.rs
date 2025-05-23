#![cfg(any(test, doc))]
//! This module exposes helpers that aid testing of CP propagators. The [`TestSolver`] allows
//! setting up specific scenarios under which to test the various operations of a propagator.
use std::fmt::Debug;

use super::propagation::constructor::PropagatorConstructor;
use super::propagation::constructor::PropagatorConstructorContext;
use super::propagation::store::PropagatorStore;
use super::propagation::EnqueueDecision;
use super::propagation::ExplanationContext;
use super::TrailedValues;
use crate::basic_types::Inconsistency;
use crate::containers::KeyGenerator;
use crate::engine::conflict_analysis::SemanticMinimiser;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::propagation::contexts::PropagationContextWithTrailedValues;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::PropagatorId;
use crate::engine::reason::ReasonStore;
use crate::engine::variables::DomainId;
use crate::engine::variables::IntegerVariable;
use crate::engine::variables::Literal;
use crate::engine::Assignments;
use crate::engine::DomainEvents;
use crate::engine::EmptyDomain;
use crate::engine::WatchListCP;
use crate::predicates::PropositionalConjunction;
use crate::proof::ConstraintTag;
use crate::proof::InferenceCode;
use crate::proof::ProofLog;

/// A container for CP variables, which can be used to test propagators.
#[derive(Debug)]
pub(crate) struct TestSolver {
    pub assignments: Assignments,
    pub propagator_store: PropagatorStore,
    pub reason_store: ReasonStore,
    pub semantic_minimiser: SemanticMinimiser,
    pub trailed_values: TrailedValues,
    watch_list: WatchListCP,
    constraint_tags: KeyGenerator<ConstraintTag>,
    inference_codes: KeyGenerator<InferenceCode>,
}

impl Default for TestSolver {
    fn default() -> Self {
        let mut solver = Self {
            assignments: Default::default(),
            reason_store: Default::default(),
            propagator_store: Default::default(),
            semantic_minimiser: Default::default(),
            watch_list: Default::default(),
            trailed_values: Default::default(),
            constraint_tags: Default::default(),
            inference_codes: Default::default(),
        };
        // We allocate space for the zero-th dummy variable at the root level of the assignments.
        solver.watch_list.grow();
        solver
    }
}

impl TestSolver {
    pub(crate) fn new_variable(&mut self, lb: i32, ub: i32) -> DomainId {
        self.watch_list.grow();
        self.assignments.grow(lb, ub)
    }

    pub(crate) fn new_literal(&mut self) -> Literal {
        let domain_id = self.new_variable(0, 1);
        Literal::new(domain_id)
    }

    pub(crate) fn new_propagator<Constructor>(
        &mut self,
        constructor: Constructor,
    ) -> Result<PropagatorId, Inconsistency>
    where
        Constructor: PropagatorConstructor,
        Constructor::PropagatorImpl: 'static,
    {
        let propagator_slot = self.propagator_store.new_propagator();

        let mut proof_log = ProofLog::default();

        let constructor_context = PropagatorConstructorContext::new(
            &mut self.watch_list,
            &mut self.trailed_values,
            &mut proof_log,
            propagator_slot.key(),
            &mut self.assignments,
        );

        let propagator = Box::new(constructor.create(constructor_context));

        let id = propagator_slot.populate(propagator);

        let context = PropagationContextMut::new(
            &mut self.trailed_values,
            &mut self.assignments,
            &mut self.reason_store,
            &mut self.semantic_minimiser,
            PropagatorId(0),
        );
        self.propagator_store[id].propagate(context)?;

        Ok(id)
    }

    pub(crate) fn contains<Var: IntegerVariable>(&self, var: Var, value: i32) -> bool {
        var.contains(&self.assignments, value)
    }

    pub(crate) fn lower_bound(&self, var: DomainId) -> i32 {
        self.assignments.get_lower_bound(var)
    }

    pub(crate) fn increase_lower_bound_and_notify(
        &mut self,
        propagator: PropagatorId,
        local_id: u32,
        var: DomainId,
        value: i32,
    ) -> EnqueueDecision {
        let result = self.assignments.tighten_lower_bound(var, value, None);
        assert!(result.is_ok(), "The provided value to `increase_lower_bound` caused an empty domain, generally the propagator should not be notified of this change!");
        let context =
            PropagationContextWithTrailedValues::new(&mut self.trailed_values, &self.assignments);
        self.propagator_store[propagator].notify(
            context,
            LocalId::from(local_id),
            OpaqueDomainEvent::from(
                DomainEvents::LOWER_BOUND
                    .get_int_events()
                    .iter()
                    .next()
                    .unwrap(),
            ),
        )
    }

    pub(crate) fn decrease_upper_bound_and_notify(
        &mut self,
        propagator: PropagatorId,
        local_id: u32,
        var: DomainId,
        value: i32,
    ) -> EnqueueDecision {
        let result = self.assignments.tighten_upper_bound(var, value, None);
        assert!(result.is_ok(), "The provided value to `increase_lower_bound` caused an empty domain, generally the propagator should not be notified of this change!");
        let context =
            PropagationContextWithTrailedValues::new(&mut self.trailed_values, &self.assignments);
        self.propagator_store[propagator].notify(
            context,
            LocalId::from(local_id),
            OpaqueDomainEvent::from(
                DomainEvents::UPPER_BOUND
                    .get_int_events()
                    .iter()
                    .next()
                    .unwrap(),
            ),
        )
    }
    pub(crate) fn is_literal_false(&self, literal: Literal) -> bool {
        self.assignments
            .evaluate_predicate(literal.get_true_predicate())
            .is_some_and(|truth_value| !truth_value)
    }

    pub(crate) fn upper_bound(&self, var: DomainId) -> i32 {
        self.assignments.get_upper_bound(var)
    }

    pub(crate) fn remove(&mut self, var: DomainId, value: i32) -> Result<(), EmptyDomain> {
        self.assignments.remove_value_from_domain(var, value, None)
    }

    pub(crate) fn set_literal(
        &mut self,
        literal: Literal,
        truth_value: bool,
    ) -> Result<(), EmptyDomain> {
        match truth_value {
            true => self
                .assignments
                .post_predicate(literal.get_true_predicate(), None),
            false => self
                .assignments
                .post_predicate((!literal).get_true_predicate(), None),
        }
    }

    pub(crate) fn propagate(&mut self, propagator: PropagatorId) -> Result<(), Inconsistency> {
        let context = PropagationContextMut::new(
            &mut self.trailed_values,
            &mut self.assignments,
            &mut self.reason_store,
            &mut self.semantic_minimiser,
            PropagatorId(0),
        );
        self.propagator_store[propagator].propagate(context)
    }

    pub(crate) fn propagate_until_fixed_point(
        &mut self,
        propagator: PropagatorId,
    ) -> Result<(), Inconsistency> {
        let mut num_trail_entries = self.assignments.num_trail_entries();
        self.notify_propagator(propagator);
        loop {
            {
                // Specify the life-times to be able to retrieve the trail entries
                let context = PropagationContextMut::new(
                    &mut self.trailed_values,
                    &mut self.assignments,
                    &mut self.reason_store,
                    &mut self.semantic_minimiser,
                    PropagatorId(0),
                );
                self.propagator_store[propagator].propagate(context)?;
                self.notify_propagator(propagator);
            }
            if self.assignments.num_trail_entries() == num_trail_entries {
                break;
            }
            num_trail_entries = self.assignments.num_trail_entries();
        }
        Ok(())
    }

    pub(crate) fn notify_propagator(&mut self, propagator: PropagatorId) {
        let events = self.assignments.drain_domain_events().collect::<Vec<_>>();
        for (event, domain) in events {
            // The nogood propagator is treated in a special way, since it is not explicitly
            // subscribed to any domain updates, but implicitly is subscribed to all updates.
            if self.propagator_store[propagator].name() == "NogoodPropagator" {
                let context = PropagationContextWithTrailedValues::new(
                    &mut self.trailed_values,
                    &self.assignments,
                );
                let local_id = LocalId::from(domain.id);
                let _ = self.propagator_store[propagator].notify(context, local_id, event.into());
            } else {
                for propagator_var in self.watch_list.get_affected_propagators(event, domain) {
                    let context = PropagationContextWithTrailedValues::new(
                        &mut self.trailed_values,
                        &self.assignments,
                    );
                    let _ = self.propagator_store[propagator].notify(
                        context,
                        propagator_var.variable,
                        event.into(),
                    );
                }
            }
        }
    }

    pub(crate) fn get_reason_int(&mut self, predicate: Predicate) -> PropositionalConjunction {
        let reason_ref = self
            .assignments
            .get_reason_for_predicate_brute_force(predicate);
        let mut predicates = vec![];
        let _ = self.reason_store.get_or_compute(
            reason_ref,
            ExplanationContext::without_working_nogood(
                &self.assignments,
                self.assignments.get_trail_position(&predicate).unwrap(),
            ),
            &mut self.propagator_store,
            &mut predicates,
        );

        PropositionalConjunction::from(predicates)
    }

    pub(crate) fn get_reason_bool(
        &mut self,
        literal: Literal,
        truth_value: bool,
    ) -> PropositionalConjunction {
        let predicate = match truth_value {
            true => literal.get_true_predicate(),
            false => (!literal).get_true_predicate(),
        };
        self.get_reason_int(predicate)
    }

    pub(crate) fn assert_bounds(&self, var: DomainId, lb: i32, ub: i32) {
        let actual_lb = self.lower_bound(var);
        let actual_ub = self.upper_bound(var);

        assert_eq!(
            (lb, ub), (actual_lb, actual_ub),
            "The expected bounds [{lb}..{ub}] did not match the actual bounds [{actual_lb}..{actual_ub}]"
        );
    }

    pub(crate) fn new_constraint_tag(&mut self) -> ConstraintTag {
        self.constraint_tags.next_key()
    }

    pub(crate) fn new_inference_code(&mut self) -> InferenceCode {
        self.inference_codes.next_key()
    }
}
