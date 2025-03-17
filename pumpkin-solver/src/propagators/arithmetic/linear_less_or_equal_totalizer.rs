use crate::basic_types::PropositionalConjunction;
use crate::basic_types::{Inconsistency, PropagationStatusCP};
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::predicates::Predicate;
use crate::variables::DomainId;
use crate::{predicate, pumpkin_assert_simple};
use itertools::Itertools;
use std::ops::Range;
use crate::basic_types::linear_options::{proxy_sort, random_shuffle, Shuffle};

/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagatorTotalizer<Var> {
    x: Box<[Var]>,
    c: i32,

    // Represents the partial sums.
    partials: Box<[Option<DomainId>]>,
    b: usize,

    shuffle_strategy: Shuffle,
}

impl<Var> LinearLessOrEqualPropagatorTotalizer<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32, shuffle_strategy: Shuffle, b: usize) -> Self {
        LinearLessOrEqualPropagatorTotalizer::<Var> {
            x,
            c,
            partials: Box::new([]),
            b,
            shuffle_strategy,
        }
    }
}

impl<Var: 'static> Propagator for LinearLessOrEqualPropagatorTotalizer<Var>
where
    Var: IntegerVariable,
{
    fn name(&self) -> &str {
        "LinearLeq"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {

        self.push_upper_bound_down(&mut context)?;
        self.push_lower_bound_down(&mut context)?;
        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        
        Ok(())
    }

    fn priority(&self) -> u32 {
        0
    }

    fn initialise_at_root(&mut self, context: &mut PropagatorInitialisationContext, ) -> Result<(), PropositionalConjunction> {
        match self.shuffle_strategy {
            Shuffle::None => {}
            Shuffle::Scalar => {self.x = proxy_sort(&self.x, &self.x.iter().map(|x| x.get_scale()).collect_vec().into_boxed_slice())}
            Shuffle::Random => {self.x = random_shuffle(&self.x, 42)}
        }

        // TODO double check this size calculation
        // Note that floating precision may bite us and create a larger tree than necessary.
        let size = (self.b as f64).powf((self.x.len() as f64).powf(1.0/(self.b as f64)).ceil()) as usize - 1;

        self.partials = vec![None; size].into_boxed_slice();

        // Note that this creates a tree like structure via an array representation.
        // this may actually mean that x is accessed in a reverse order however this does not violate the tree structure.
        for i in (0..size).rev() {
            let is_left_child_valid = self.node_exists(self.children(i).next().unwrap());
            if !is_left_child_valid {
                continue;
            }
            
            let lb: i32 = self.children(i).filter_map(|j| self.get_lower_init(context, j)).sum();
            let mut ub: i32 = self.children(i).filter_map(|j| self.get_upper_init(context, j)).sum();
            
            if i == 0 {
                if self.c < lb {
                    return Err(PropositionalConjunction::from(self.children(i).filter_map(|j| self.get_pred_lower_init(context, j)).collect_vec()));
                }
                ub = self.c;
            }

            pumpkin_assert_simple!(lb <= ub, "Cannot create variables with inconsistent domains, ub < lb for index {i}, lb: {lb} ub: {ub}");

            let partial = context.create_new_integer_variable(lb, ub);
            
            self.partials[i] = Some(partial);
            let _ = context.register(
                partial.clone(),
                DomainEvents::BOUNDS,
                LocalId::from(i as u32),
            );
        }

        self.x.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::BOUNDS,
                LocalId::from((i + size) as u32),
            );
        });
        
        Ok(())
    }
}



impl<Var: 'static> LinearLessOrEqualPropagatorTotalizer<Var>
where
    Var: IntegerVariable,
{
    
    /// Returns true if the index is accessible in the tree structure,
    /// False otherwise.
    fn node_exists(&self, index: usize) -> bool {
        if index >= self.partials.len() {
            index - self.partials.len() < self.x.len()
        } else {
            match self.partials[index] {
                None => false,
                Some(_) => true,
            }
        }
    }

    /// Returns the lower bound of the variable at index i 
    fn get_lower(&self, context: &PropagationContextMut, index: usize) -> Option<i32> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(context.lower_bound(x)),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(context.lower_bound(&x))
            }
        }
    }

    /// Returns the lower bound of the variable at index i 
    fn get_lower_init(&self, context: &PropagatorInitialisationContext, index: usize) -> Option<i32> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(context.lower_bound(x)),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(context.lower_bound(&x))
            }
        }
    }

    /// Returns the upper bound of the variable at index i
    fn get_upper(&self, context: &PropagationContextMut, index: usize) -> Option<i32> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(context.upper_bound(x)),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(context.upper_bound(&x))
            }
        }
    }

    /// Returns the upper bound of the variable at index i
    fn get_upper_init(&self, context: &PropagatorInitialisationContext, index: usize) -> Option<i32> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(context.upper_bound(x)),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(context.upper_bound(&x))
            }
        }
    }

    /// Sets the lower bound of the variable at index i
    fn set_lower(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_lower_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_lower_bound(&self.partials[index].unwrap(), bound, reason)?;
        }
        Ok(())
    }

    /// Sets the upper bound of the variable at index i
    fn set_upper(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_upper_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_upper_bound(&self.partials[index].unwrap(), bound, reason)?;
        }
        Ok(())
    }

    /// Returns a lower bound predicate for the variable at index i.
    fn get_pred_lower(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] >= context.lower_bound(&self.x[index - self.partials.len()]))
        } else {
            let node = self.partials[index].unwrap();
            predicate!(node >= context.lower_bound(&node))
        }
    }

    /// Returns a lower bound predicate for the variable at index i.
    fn get_pred_lower_init(&self, context: &PropagatorInitialisationContext, index: usize) -> Option<Predicate> {
        if !self.node_exists(index) {
            return None;
        }
        if index >= self.partials.len() {
            Some(predicate!(self.x[index - self.partials.len()] >= context.lower_bound(&self.x[index - self.partials.len()])))
        } else {
            let node = self.partials[index].unwrap();
            Some(predicate!(node >= context.lower_bound(&node)))
        }
    }

    /// Returns an upper bound predicate for the variable at index i.
    fn get_pred_upper(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] <= context.upper_bound(&self.x[index - self.partials.len()]))
        } else {
            let node = self.partials[index].unwrap();
            predicate!(node <= context.upper_bound(&node))
        }
    }

    /// Returns the range of child indices for the parent at index.
    fn children(&self, index: usize) -> Range<usize> {
        (index*self.b + 1)..(index*self.b + self.b + 1)
    }

    /// Given a consumption by the leaf nodes, push this information back up to the root node.
    /// Simply each child node states the minimum consumption of the branch.
    fn push_lower_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in (0..self.partials.len()).rev() {
            if !self.node_exists(i) {
                continue;
            }
            let lb: i32 = self.children(i).filter_map(|j| self.get_lower(context, j)).sum();

            // Quick return in case of error, we do not rely on Empty domain default error behaviour.
            if lb > self.get_upper(context, i).unwrap() {
                let mut reason: PropositionalConjunction = self.children(i).filter(|j| self.node_exists(*j)).map(|j| self.get_pred_lower(context, j)).collect();
                reason.push(self.get_pred_upper(context, i));
                return Err(Inconsistency::from(reason))
            }
            
            if lb > self.get_lower(context, i).unwrap() {

                let reason: PropositionalConjunction = self.children(i).filter(|j| self.node_exists(*j)).map(|j| self.get_pred_lower(context, j)).collect();

                self.set_lower(context, i, lb, reason)?
            }
        }
        Ok(())
    }

    /// Given that all the leaves have an upper bound, the upperbound of the parent node should be set to this value
    fn push_upper_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in (0..self.partials.len()).rev() {
            if !self.node_exists(i) {
                continue;
            }
            let ub: i32 = self.children(i).filter_map(|j| self.get_upper(context, j)).sum();

            // Quick return in case of error, we do not rely on Empty domain default error behaviour.
            if ub < self.get_lower(context, i).unwrap() {
                let mut reason: PropositionalConjunction = self.children(i).filter(|j| self.node_exists(*j)).map(|j| self.get_pred_upper(context, j)).collect();
                reason.push(self.get_pred_lower(context, i));
                return Err(Inconsistency::from(reason))
            }
            
            if ub < self.get_upper(context, i).unwrap() {
                let reason: PropositionalConjunction = self.children(i).filter(|j| self.node_exists(*j)).map(|j| self.get_pred_upper(context, j)).collect();
                self.set_upper(context, i, ub, reason)?
            }
        }
        Ok(())
    }


    /// Given a max capacity of a node and the consumption of its neighbours
    /// Set the upperbound for the remaining consumption.
    fn push_upper_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in 0..self.partials.len() {
            if !self.node_exists(i) {
                continue;
            }
            let total_bound = self.get_upper(context, i).unwrap() - self.children(i).filter_map(|j|self.get_lower(context, j)).sum::<i32>();
            
            for j in self.children(i) {
                if !self.node_exists(j) {
                    continue;
                }
                let new_bound = total_bound + self.get_lower(context, j).unwrap();

                // Quick return in case of error, we do not rely on Empty domain default error behaviour.
                if new_bound < self.get_lower(context, j).unwrap() {
                    let mut reason: PropositionalConjunction = self.children(i).filter(|k| self.node_exists(*k))
                        .map(|k| self.get_pred_lower(context, k)).collect();
                    reason.push(self.get_pred_upper(context, i));
                    return Err(Inconsistency::from(reason))
                }
                
                if new_bound < self.get_upper(context, j).unwrap() {
                    let mut reason: PropositionalConjunction = self.children(i).filter(|k| self.node_exists(*k))
                        .filter_map(|k| if j != k {Some(self.get_pred_lower(context, k))} else {None}).collect();
                    reason.push(self.get_pred_upper(context, i));
                    self.set_upper(context, j, new_bound, reason)?;
                }
            }
        }
        Ok(())
    }

    /// Given a mandatory amount of consumption and a maximum amount of consumption from the neighbours
    /// Set the lower bound of a nodes' consumption.
    fn push_lower_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in 0..self.partials.len() {
            if !self.node_exists(i) {
                continue;
            }
            let total_bound = self.get_lower(context, i).unwrap() - self.children(i).filter_map(|j|self.get_upper(context, j)).sum::<i32>();
            
            for j in self.children(i) {
                if !self.node_exists(j) {
                    continue;
                }
                let new_bound = total_bound + self.get_upper(context, j).unwrap();

                // Quick return in case of error, we do not rely on Empty domain default error behaviour.
                if new_bound > self.get_upper(context, j).unwrap() {
                    let mut reason: PropositionalConjunction = self.children(i).filter(|k| self.node_exists(*k))
                        .map(|k| self.get_pred_upper(context, k)).collect();
                    reason.push(self.get_pred_lower(context, i));
                    return Err(Inconsistency::from(reason))
                }
                
                if new_bound > self.get_lower(context, j).unwrap() {
                    let mut reason: PropositionalConjunction = self.children(i).filter(|k| self.node_exists(*k))
                        .filter_map(|k| if j != k {Some(self.get_pred_upper(context, k))} else {None}).collect();
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
    use crate::engine::propagation::EnqueueDecision;
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([z,z1, x2, x, y, p].into(), 12, Shuffle::None, 2))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        let decision = solver.increase_lower_bound_and_notify(propagator, 1, z1, 2);
        match decision {
            EnqueueDecision::Enqueue => {solver.propagate(propagator).expect("non-empty domain");}
            EnqueueDecision::Skip => {}
        }
        
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), 7, Shuffle::None, 2))
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), i32::MAX, Shuffle::None, 2))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), i32::MIN, Shuffle::None, 2))
            .expect("Expected no error to be detected");
    }
}
