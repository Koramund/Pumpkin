use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::predicate;
use crate::predicates::Predicate;
use crate::variables::DomainId;
use itertools::Itertools;
use std::cmp::min;
use std::ops::Range;
use num::integer::{div_ceil, nth_root, sqrt};
use num::pow;

/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagator<Var> {
    x: Box<[Var]>,
    c: i32,

    // Represents the partial sums.
    partials: Box<[Option<DomainId>]>,
    b: usize,

    // any index we want to index needs to be checked against this, should be strictly less for the index to be valid.
    // Either that or we do everything with options and filter maps.
    total_num: usize,
}

impl<Var> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32) -> Self {
        let b = 2;
        let total_num = x.len();

        LinearLessOrEqualPropagator::<Var> {
            x,
            c,
            partials: Box::new([]),
            b,
            total_num,
        }
    }
}

impl<Var: 'static> Propagator for LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    fn initialise_at_root(&mut self, context: &mut PropagatorInitialisationContext, ) -> Result<(), PropositionalConjunction> {

        // We create our tree structure in an array based encoding
        // This sets up the initial layer of the incoming x variables.
        let mut partials = Vec::new();
        let mut orphan_partials = Vec::new();
        // self.x = self.x.iter().rev().cloned().collect_vec().into();

        let lb: i32 = self.x.iter().map(|x| context.lower_bound(x)).filter(|x| x.is_negative()).sum();
        let ub: i32 = self.x.iter().map(|x| context.upper_bound(x)).filter(|x| x.is_positive()).sum();
        
        for chunk in self.x.chunks(self.b) {
            // let lb = chunk.iter().map(|x| context.lower_bound(x)).sum();
            // let ub = chunk.iter().map(|x| context.upper_bound(x)).sum();

            let partial = context.create_new_integer_variable(lb, ub);

            let _ = context.register(
                partial.clone(),
                DomainEvents::BOUNDS,
                LocalId::from((i + self.x.len()) as u32),
            );

            partials.push(partial);
            orphan_partials.push(partial);
        }
        
        // TODO double check this size calculation
        let size = pow(div_ceil(nth_root(self.x.len(), self.b as u32), 1), self.b) - 1;
        self.partials = vec![None; size].into_boxed_slice();
        
        for i in (0..size).rev() {
            // TODO change the get methods to also return options such that filter maps automatically ignore it :P
            let lb: i32 = self.children(i).filter_map(|j| self.get_lower(context, i)).sum();
            let ub: i32 = self.children(i).filter_map(|j| self.get_upper(context, i)).sum();

            let partial = context.create_new_integer_variable(lb, ub);
            self.partials[i] = Some(partial);
        }
        
        
        // This then keeps building new layers until no more new layers are required.
        while orphan_partials.len() > self.b {
            let mut new_orphans = Vec::new();

            for (i, chunk) in orphan_partials.chunks(self.b).enumerate() {
                // let lb = chunk.iter().map(|x| context.lower_bound(x)).sum();
                // let ub = chunk.iter().map(|x| context.upper_bound(x)).sum();

                let partial = context.create_new_integer_variable(lb, ub);

                let _ = context.register(
                    partial.clone(),
                    DomainEvents::BOUNDS,
                    LocalId::from((i + self.x.len()) as u32),
                );

                partials.push(partial);
                new_orphans.push(partial);
            }
            
            
            
            orphan_partials = new_orphans;
        }

        // we then add the final partial node.
        // This has the upperbound of self.c, which we will now no longer utilize during any actual propagation.

        let partial = context.create_new_integer_variable(lb, self.c);
        let _ = context.register(
            partial.clone(),
            DomainEvents::BOUNDS,
            LocalId::from((partials.len() + self.x.len()) as u32),
        );

        partials.push(partial);

        // An array based complete tree structure requires the root to be at index 0
        // However, because we built-bottoms up this means we need to reverse our entire array setup once done.
        // While we do not care about this for notifying it is nice to set it up properly
        // TODO is the cloning a risk?
        self.partials = partials.iter().rev().cloned().collect_vec().into();
        

        // Then register to our nodes but now with their correct array based local indices.
        self.partials.iter().enumerate().for_each(|(i, partial)| {
            let _ = context.register(
                partial.clone(),
                DomainEvents::BOUNDS,
                LocalId::from(i as u32),
            );
        });

        self.x.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::BOUNDS,
                LocalId::from((i + self.partials.len()) as u32),
            );
        });

        self.total_num = self.partials.len() + self.x.len();

        Ok(())
    }

    fn priority(&self) -> u32 {
        0
    }

    fn name(&self) -> &str {
        "LinearLeq"
    }
        
    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {

        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_down(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        self.push_lower_bound_down(&mut context)?;


        Ok(())
    }
}



impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{

    // a series of functions such that I do not need to think about what the value of value i actually references
    fn get_lower(&self, context: &PropagationContextMut, index: usize) -> i32 {
        if index >= self.partials.len() {
            context.lower_bound(&self.x[index - self.partials.len()])
        } else {
            context.lower_bound(&self.partials[index])
        }
    }

    fn get_upper(&self, context: &PropagationContextMut, index: usize) -> i32 {
        if index >= self.partials.len() {
            context.upper_bound(&self.x[index - self.partials.len()])
        } else {
            context.upper_bound(&self.partials[index])
        }
    }

    fn set_lower(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_lower_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_lower_bound(&self.partials[index], bound, reason)?;
        }
        Ok(())
    }

    fn set_upper(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_upper_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_upper_bound(&self.partials[index], bound, reason)?;
        }
        Ok(())
    }

    fn get_pred_lower(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] >= context.lower_bound(&self.x[index - self.partials.len()]))
        } else {
            predicate!(self.partials[index] >= context.lower_bound(&self.partials[index]))
        }
    }

    fn get_pred_upper(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] <= context.upper_bound(&self.x[index - self.partials.len()]))
        } else {
            predicate!(self.partials[index] <= context.upper_bound(&self.partials[index]))
        }
    }

    /// If there are any out of bounds errors, blame this little guy here.
    fn children(&self, index: usize) -> Range<usize> {
        (index*self.b + 1)..min(index*self.b + self.b + 1, self.total_num)
    }

    fn parent_index(&self, index: usize) -> usize {
        (index - 1) / self.b
    }


    /// Given a consumption by the leaf nodes, push this information back up to the root node.
    /// Simply each child node stipulates the minimum consumption of the branch.
    fn push_lower_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // this one is rather simple.
        for i in (0..self.partials.len()).rev() {
            let lb: i32 = self.children(i).map(|j| self.get_lower(context, j)).sum();

            if lb > self.get_lower(context, i) {

                let reason: PropositionalConjunction = self.children(i).map(|j| self.get_pred_lower(context, j)).collect();

                self.set_lower(context, i, lb, reason)?
            }
        }
        Ok(())
    }

    /// Given that all the leaves have an upper bound, the upperbound of the parent node should be set to this value
    fn push_upper_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in (0..self.partials.len()).rev() {
            let ub: i32 = self.children(i).map(|j| self.get_upper(context, j)).sum();

            if ub < self.get_upper(context, i) {

                let reason: PropositionalConjunction = self.children(i).map(|j| self.get_pred_upper(context, j)).collect();

                self.set_upper(context, i, ub, reason)?
            }
        }
        Ok(())
    }


    /// Given a max capacity of a node and the consumption of its neighbours
    /// Set the upperbound for the remaining consumption.
    fn push_upper_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // each partial updates the nodes below it. This is because the upperbound of the root node cannot be changed by this type of propagation.

        for i in 0..self.partials.len() {
            // a propagation is responsible for checking the upperbound of the current node
            // then subtracting the lower bound of the neighbours.
            // this then becomes the new upperbound for the node i
            let total_bound = self.get_upper(context, i) - self.children(i).map(|j|self.get_lower(context, j)).sum::<i32>();
            for j in self.children(i) {
                let new_bound = total_bound + self.get_lower(context, j);
                // dbg!((i,j,total_bound, new_bound, self.children(i).map(|j|self.get_lower(context, j)).collect_vec()), self.children(i));
                if new_bound < self.get_upper(context, j) {

                    let mut reason: PropositionalConjunction = self.children(i)
                        .filter_map(|k| if j != k {Some(self.get_pred_lower(context, j))} else {None}).collect();

                    reason.push(self.get_pred_upper(context, i));

                    self.set_upper(context, j, new_bound, reason)?;
                }
            }
        }
        Ok(())
    }

    /// Given a mandatory amount of consumption and a maximum amount of consumption from the neighbours
    /// Set the lowerbound of a nodes consumption.
    fn push_lower_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // each partial updates the nodes below it. This is because the upperbound of the root node cannot be changed by this type of propagation.

        for i in 0..self.partials.len() {
            // this deals with the concept of mandatory consumption
            // the root node has some lower bound of consumption that must take place.
            // this means that your lowerbound = mandatory - maximum of your neighbours
            // it is probably a weak propagation but who knows, could be interesting.

            // a propagation is responsible for checking the upperbound of the current node
            // then subtracting the lower bound of the neighbours.
            // this then becomes the new upperbound for the node i
            let total_bound = self.get_lower(context, i) - self.children(i).map(|j|self.get_upper(context, j)).sum::<i32>();
            for j in self.children(i) {
                let new_bound = total_bound + self.get_upper(context, j);
                if new_bound > self.get_lower(context, j) {

                    let mut reason: PropositionalConjunction = self.children(i)
                        .filter_map(|k| if j != k {Some(self.get_pred_upper(context, j))} else {None}).collect();

                    reason.push(self.get_pred_lower(context, i));

                    self.set_lower(context, j, new_bound, reason)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conjunction;
    use crate::engine::test_solver::TestSolver;

    #[test]
    fn test_bounds_are_propagated() {
        let mut solver = TestSolver::default();
        let z = solver.new_variable(2, 8);
        let z1 = solver.new_variable(0, 7);
        let x2 = solver.new_variable(2, 5);
        let x = solver.new_variable(1, 5);
        let y = solver.new_variable(0, 10);
        let p = solver.new_variable(1, 5);

        let propagator = solver
            .new_propagator(LinearLessOrEqualPropagator::new([z,z1, x2, x, y, p].into(), 12))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");
        
        solver.increase_lower_bound_and_notify(propagator, 1, z1, 2);

        solver.propagate(propagator).expect("non-empty domain");

        println!("{:?}", solver.reason_store);

        println!("{}", solver.get_reason_int(predicate!(y <= 6)));

        solver.assert_bounds(z, 2, 6);
        solver.assert_bounds(z1, 2, 6);
        solver.assert_bounds(x2, 2, 5);
        solver.assert_bounds(x, 1, 5);
        solver.assert_bounds(y, 0, 4);
        solver.assert_bounds(p, 1, 5);
    }

    #[test]
    fn test_explanations() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(1, 5);
        let y = solver.new_variable(0, 10);

        let propagator = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), 7))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        let reason = solver.get_reason_int(predicate![y <= 6]);
        
        assert_eq!(conjunction!([x >= 1]), reason);
    }

    #[test]
    fn overflow_leads_to_conflict() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MAX, i32::MAX);
        let y = solver.new_variable(1, 1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), i32::MAX))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagator::new([x, y].into(), i32::MIN))
            .expect("Expected no error to be detected");
    }
}
