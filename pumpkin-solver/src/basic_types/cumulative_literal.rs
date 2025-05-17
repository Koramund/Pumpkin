use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessOrEqualMinimumPropagator;
use crate::propagators::ReifiedPropagator;
use crate::variables::{AffineView, DomainId};


type Affine = AffineView<DomainId>;
type ReifiedLE = ReifiedPropagator<LessOrEqualMinimumPropagator<Affine, Affine>>;
type ReifiedGE = ReifiedPropagator<LargerOrEqualMinimumPropagator<Affine, Affine>>;

/// They are given separate var definitions as Var1 may not be an affineView but Var2 may be and vice versa
/// This depends on the shift they have partaken in
#[derive(Debug)]
pub(crate) struct CumulativeLiteral {
    pub prop1: ReifiedLE,
    pub prop2: ReifiedGE
}

impl CumulativeLiteral {
    pub fn new(prop1: ReifiedLE, prop2: ReifiedGE) -> Self {
        Self { prop1, prop2 }
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
    pub fn new(is_lower_bound: bool, shifted_task: u32, conflicting_tasks: Vec<u32>) -> Self {
        MapToLiteral{is_lower_bound, shifted_task, conflicting_tasks}
    }
}