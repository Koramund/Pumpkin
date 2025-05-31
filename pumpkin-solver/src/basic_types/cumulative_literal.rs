use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessThanMinimumPropagator;
use crate::propagators::ReifiedPropagator;
use crate::variables::AffineView;
use clap::ValueEnum;
use crate::engine::propagation::PropagatorId;

type Affine = AffineView;
type ReifiedLE = ReifiedPropagator<LessThanMinimumPropagator<Affine, Affine>>;
pub(crate) type ReifiedGE = ReifiedPropagator<LargerOrEqualMinimumPropagator<Affine, Affine>>;

/// They are given separate var definitions as Var1 may not be an affineView but Var2 may be and vice versa
/// This depends on the shift they have partaken in
#[derive(Debug)]
pub(crate) struct CumulativeLiteral {
    pub prop1: ReifiedGE,
    pub prop2: ReifiedLE,
    pub id1: PropagatorId,
    pub id2: PropagatorId,
}

impl CumulativeLiteral {
    pub(crate) fn new(prop1: ReifiedGE, prop2: ReifiedLE, id1: PropagatorId, id2: PropagatorId) -> Self {
        Self { prop1, prop2, id1, id2 }
    }
}


/// This struct is utilized as the key to the global map
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct MapToLiteral {
    pub is_lower_bound: bool,
    pub shifted_task: u32,
    pub conflicting_tasks: Vec<u32>,
}

impl MapToLiteral {
    pub(crate) fn new(is_lower_bound: bool, shifted_task: u32, mut conflicting_tasks: Vec<u32>) -> Self {
        conflicting_tasks.sort();
        MapToLiteral{is_lower_bound, shifted_task, conflicting_tasks}
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
