use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::ReifiedPropagator;
use crate::variables::AffineView;
use clap::ValueEnum;
use crate::engine::propagation::PropagatorId;

pub(crate) type ReifiedGE = ReifiedPropagator<LargerOrEqualMinimumPropagator<AffineView, AffineView>>;

/// They are given separate var definitions as Var1 may not be an affineView but Var2 may be and vice versa
/// This depends on the shift they have partaken in
#[derive(Debug, Clone)]
pub(crate) struct CumulativeLiteral {
    pub lb_propagator: ReifiedGE,
    pub ub_propagator: ReifiedGE,
    pub lb_id: PropagatorId,
    pub ub_id: PropagatorId,
}

impl CumulativeLiteral {
    pub(crate) fn new(lb_propagator: ReifiedGE, ub_propagator: ReifiedGE, lb_id: PropagatorId, ub_id: PropagatorId) -> Self {
        Self { lb_propagator, ub_propagator, lb_id, ub_id }
    }
}


/// This struct is utilized as the key to the global map
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct MapToLiteral {
    pub shifted_task: u32,
    pub conflicting_tasks: Vec<u32>,
}

impl MapToLiteral {
    pub(crate) fn new(shifted_task: u32, mut conflicting_tasks: Vec<u32>) -> Self {
        conflicting_tasks.sort();
        MapToLiteral{shifted_task, conflicting_tasks}
    }
}

/// This denotes the underlying supports that will be used when creating explanations for the extended resolution.
#[derive(Debug, PartialEq, Eq, ValueEnum, Copy, Clone, Default)]
pub enum CumulativeExtendedType {
    Naive,
    BigStep,
    #[default]
    PointWise,
}
