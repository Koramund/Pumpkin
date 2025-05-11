use crate::basic_types::linear_options::LinearInequalityType;
use crate::constraints::Constraint;
use crate::constraints::NegatableConstraint;
use crate::propagators::linear_less_or_equal_default::LinearLessOrEqualPropagatorDefault;
use crate::propagators::linear_less_or_equal_sequential::LinearLessOrEqualPropagatorSequential;
use crate::propagators::linear_less_or_equal_totalizer::LinearLessOrEqualPropagatorTotalizer;
use crate::variables::{AffineView, DomainId, IntegerVariable};
use crate::ConstraintOperationError;
use crate::Solver;
use std::collections::HashMap;
use std::num::NonZero;
use std::sync::{LazyLock, Mutex};

// Maps a series of offset, scale, inner id to a corresponding partial sum variable.
// Currently, we'll mark offset to 0 until the thing is expanded.
pub static PARTIAL_ENCODINGS: LazyLock<Mutex<HashMap<Vec<(i32, i32, u32)>, AffineView<DomainId>>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub static DECOMPOSED: LazyLock<Mutex<HashMap<u32, Vec<u32>>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

/// Create the [`NegatableConstraint`] `\sum terms_i <= rhs`.
///
/// Its negation is `\sum terms_i > rhs`
pub fn less_than_or_equals<Var: IntegerVariable + 'static>(
    terms: impl Into<Box<[Var]>>,
    rhs: i32,
) -> impl NegatableConstraint {
    Inequality {
        terms: terms.into(),
        rhs,
    }
}

/// Creates the [`NegatableConstraint`] `lhs <= rhs`.
///
/// Its negation is `lhs > rhs`.
pub fn binary_less_than_or_equals<Var: IntegerVariable + 'static>(
    lhs: Var,
    rhs: Var,
) -> impl NegatableConstraint {
    less_than_or_equals([lhs.scaled(1), rhs.scaled(-1)], 0)
}

/// Creates the [`NegatableConstraint`] `lhs < rhs`.
///
/// Its negation is `lhs >= rhs`.
pub fn binary_less_than<Var: IntegerVariable + 'static>(
    lhs: Var,
    rhs: Var,
) -> impl NegatableConstraint {
    binary_less_than_or_equals(lhs.scaled(1), rhs.offset(-1))
}

struct Inequality<Var> {
    terms: Box<[Var]>,
    rhs: i32,
}

impl<Var: IntegerVariable + 'static> Constraint for Inequality<Var> {
    fn post(
        self,
        solver: &mut Solver,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        if self.terms.len() < 4 {
            LinearLessOrEqualPropagatorDefault::new(self.terms, self.rhs).post(solver, tag)
        } else {
            match solver.satisfaction_solver.internal_parameters.linear_inequality_type {
                LinearInequalityType::Incremental => {LinearLessOrEqualPropagatorDefault::new(self.terms, self.rhs).post(solver, tag)},
                LinearInequalityType::Sequential => {LinearLessOrEqualPropagatorSequential::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, false).post(solver, tag)}
                LinearInequalityType::Totalizer => {LinearLessOrEqualPropagatorTotalizer::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, false).post(solver, tag)},
            }
        }
    }

    fn implied_by(
        self,
        solver: &mut Solver,
        reification_literal: crate::variables::Literal,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        LinearLessOrEqualPropagatorDefault::new(self.terms, self.rhs).implied_by(
            solver,
            reification_literal,
            tag,
        )
    }
}

impl<Var: IntegerVariable + 'static> NegatableConstraint for Inequality<Var> {
    type NegatedConstraint = Inequality<Var::AffineView>;

    fn negation(&self) -> Self::NegatedConstraint {
        Inequality {
            terms: self.terms.iter().map(|term| term.scaled(-1)).collect(),
            rhs: -self.rhs - 1,
        }
    }
}
