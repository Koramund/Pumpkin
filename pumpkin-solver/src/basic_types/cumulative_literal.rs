use crate::propagators::larger_or_equal_to_minimum::LargerOrEqualMinimumPropagator;
use crate::propagators::less_or_equal_minimum::LessOrEqualMinimumPropagator;
use crate::propagators::ReifiedPropagator;
use crate::variables::{AffineView, DomainId};

/// They are given separate var definitions as Var1 may not be an affineView but Var2 may be and vice versa
/// This depends on the shift they have partaken in
#[derive(Debug)]
pub(crate) struct CumulativeLiteral {
    pub prop1: ReifiedPropagator<LessOrEqualMinimumPropagator<AffineView<DomainId>, AffineView<DomainId>>>,
    pub prop2: ReifiedPropagator<LargerOrEqualMinimumPropagator<AffineView<DomainId>, AffineView<DomainId>>>
    
}
