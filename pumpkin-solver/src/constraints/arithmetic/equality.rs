use super::less_than_or_equals;
use crate::constraints::Constraint;
use crate::constraints::NegatableConstraint;
use crate::propagators::linear_less_or_equal_totalizer::LinearLessOrEqualPropagatorTotalizer;
use crate::propagators::linear_not_equal::LinearNotEqualPropagator;
use crate::variables::IntegerVariable;
use crate::variables::Literal;
use crate::ConstraintOperationError;
use crate::Solver;
use std::num::NonZero;
use crate::basic_types::linear_options::LinearInequalityType;
use crate::propagators::linear_less_or_equal_sequential::LinearLessOrEqualPropagatorSequential;

/// Creates the [`NegatableConstraint`] `\sum terms_i = rhs`.
///
/// Its negation is [`not_equals`].
pub fn equals<Var: IntegerVariable + Clone + 'static>(
    terms: impl Into<Box<[Var]>>,
    rhs: i32,
) -> impl NegatableConstraint {
    EqualConstraint {
        terms: terms.into(),
        rhs,
    }
}

/// Creates the [`NegatableConstraint`] `lhs = rhs`.
///
/// Its negation is [`binary_not_equals`].
pub fn binary_equals<Var: IntegerVariable + 'static>(
    lhs: Var,
    rhs: Var,
) -> impl NegatableConstraint {
    equals([lhs.scaled(1), rhs.scaled(-1)], 0)
}

/// Create the [`NegatableConstraint`] `\sum terms_i != rhs`.
///
/// Its negation is [`equals`].
pub fn not_equals<Var: IntegerVariable + Clone + 'static>(
    terms: impl Into<Box<[Var]>>,
    rhs: i32,
) -> impl NegatableConstraint {
    equals(terms, rhs).negation()
}

/// Creates the [`NegatableConstraint`] `lhs != rhs`.
///
/// Its negation is [`binary_equals`].
pub fn binary_not_equals<Var: IntegerVariable + 'static>(
    lhs: Var,
    rhs: Var,
) -> impl NegatableConstraint {
    not_equals([lhs.scaled(1), rhs.scaled(-1)], 0)
}

struct EqualConstraint<Var> {
    terms: Box<[Var]>,
    rhs: i32,
}

impl<Var> Constraint for EqualConstraint<Var>
where
    Var: IntegerVariable + Clone + 'static,
{
    fn post(
        self,
        solver: &mut Solver,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        
        if solver.satisfaction_solver.internal_parameters.proper_equality {
            let generality = solver.satisfaction_solver.internal_parameters.linear_group_size;
            match (solver.satisfaction_solver.internal_parameters.linear_inequality_type, self.terms.len())  {
                // No proper EQ of the incremental approach exists small duplication with the code below.
                (LinearInequalityType::Sequential, terms) if terms > generality => {return LinearLessOrEqualPropagatorSequential::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, true).post(solver, tag)}
                (LinearInequalityType::Totalizer, terms) if terms > generality => {return LinearLessOrEqualPropagatorTotalizer::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, true).post(solver, tag)},
                _ => {}
            }
        }
        less_than_or_equals(self.terms.clone(), self.rhs).post(solver, tag)?;

        let negated = self
            .terms
            .iter()
            .map(|var| var.scaled(-1))
            .collect::<Box<[_]>>();
        less_than_or_equals(negated, -self.rhs).post(solver, tag)?;

        Ok(())
    
    }

    fn implied_by(
        self,
        solver: &mut Solver,
        reification_literal: Literal,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        
        if solver.satisfaction_solver.internal_parameters.proper_equality {
            // LinearLessOrEqualPropagatorTotalizer::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, true).post(solver, tag)
            let generality = solver.satisfaction_solver.internal_parameters.linear_group_size;
            match (solver.satisfaction_solver.internal_parameters.linear_inequality_type, self.terms.len())  {
                (LinearInequalityType::Sequential, terms) if terms > generality => {return LinearLessOrEqualPropagatorSequential::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, true).implied_by(solver, reification_literal, tag, )}
                (LinearInequalityType::Totalizer, terms) if terms > generality => {return LinearLessOrEqualPropagatorTotalizer::new(self.terms, self.rhs, solver.satisfaction_solver.internal_parameters.linear_ordering.clone(), solver.satisfaction_solver.internal_parameters.linear_group_size, true).implied_by(solver, reification_literal, tag, )},
                _ => {}
            }
        }
        less_than_or_equals(self.terms.clone(), self.rhs).implied_by(
            solver,
            reification_literal,
            tag,
        )?;

        let negated = self
            .terms
            .iter()
            .map(|var| var.scaled(-1))
            .collect::<Box<[_]>>();
        less_than_or_equals(negated, -self.rhs).implied_by(
            solver,
            reification_literal,
            tag,
        )?;

        Ok(())
        
    }
}

impl<Var> NegatableConstraint for EqualConstraint<Var>
where
    Var: IntegerVariable + Clone + 'static,
{
    type NegatedConstraint = NotEqualConstraint<Var>;

    fn negation(&self) -> Self::NegatedConstraint {
        NotEqualConstraint {
            terms: self.terms.clone(),
            rhs: self.rhs,
        }
    }
}

struct NotEqualConstraint<Var> {
    terms: Box<[Var]>,
    rhs: i32,
}

impl<Var> Constraint for NotEqualConstraint<Var>
where
    Var: IntegerVariable + Clone + 'static,
{
    fn post(
        self,
        solver: &mut Solver,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        LinearNotEqualPropagator::new(self.terms, self.rhs).post(solver, tag)
    }

    fn implied_by(
        self,
        solver: &mut Solver,
        reification_literal: Literal,
        tag: Option<NonZero<u32>>,
    ) -> Result<(), ConstraintOperationError> {
        LinearNotEqualPropagator::new(self.terms, self.rhs).implied_by(
            solver,
            reification_literal,
            tag,
        )
    }
}

impl<Var> NegatableConstraint for NotEqualConstraint<Var>
where
    Var: IntegerVariable + Clone + 'static,
{
    type NegatedConstraint = EqualConstraint<Var>;

    fn negation(&self) -> Self::NegatedConstraint {
        EqualConstraint {
            terms: self.terms.clone(),
            rhs: self.rhs,
        }
    }
}
