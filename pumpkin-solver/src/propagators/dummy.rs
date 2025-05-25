use crate::basic_types::PropagationStatusCP;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::predicates::PropositionalConjunction;

/// Just an empty propagator
#[derive(Clone, Debug)]
pub(crate) struct DummyPropagator {

}

impl DummyPropagator {
    pub(crate) fn new() -> Self {
        Self {
        }
    }
}

impl Propagator for DummyPropagator {
    fn priority(&self) -> u32 {
        3
    }

    fn name(&self) -> &str {
        "Dummy"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut _context: PropagationContextMut,
    ) -> PropagationStatusCP {

        Ok(())
    }

    fn initialise_at_root(
        &mut self,
        _context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        Ok(())
    }
}





