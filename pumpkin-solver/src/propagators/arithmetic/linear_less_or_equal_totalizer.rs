use crate::basic_types::linear_options::{proxy_sort, random_shuffle, Shuffle};
use crate::basic_types::PropositionalConjunction;
use crate::basic_types::{Inconsistency, PropagationStatusCP};
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::predicates::Predicate;
use crate::variables::{AffineView, DomainId, TransformableVariable};
use crate::{predicate, pumpkin_assert_simple};
use itertools::Itertools;
use std::ops::Range;
use crate::constraints::PARTIAL_ENCODINGS;

/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagatorTotalizer<Var> {
    x: Box<[Var]>,
    c: i32,
    equality: bool,

    // Represents the partial sums.
    partials: Box<[Option<AffineView<DomainId>>]>,
    b: usize,

    shuffle_strategy: Shuffle,
}

impl<Var> LinearLessOrEqualPropagatorTotalizer<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32, shuffle_strategy: Shuffle, b: usize, equality: bool) -> Self {
        LinearLessOrEqualPropagatorTotalizer::<Var> {
            x,
            c,
            equality,
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
        self.initial_constraint(&mut context)?;
        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        self.push_upper_bound_down(&mut context)?;
        self.push_lower_bound_down(&mut context)?;
        
        Ok(())
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        self.initial_constraint(&mut context)?;
        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        self.push_upper_bound_down(&mut context)?;
        self.push_lower_bound_down(&mut context)?;

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
        
        let mut cache = PARTIAL_ENCODINGS.lock().unwrap();
        
        // TODO double check this size calculation
        // Note that floating precision may bite us and create a larger tree than necessary.
        let height = (self.x.len() as f64).log(self.b as f64).ceil() as u32;
        let size = (((self.b.pow(height) - 1) as f64) / ((self.b - 1) as f64).ceil()) as usize;

        self.partials = vec![None; size].into_boxed_slice();

        // Note that this creates a tree like structure via an array representation.
        // this may actually mean that x is accessed in a reverse order however this does not violate the tree structure.
        for i in (0..size).rev() {
            let is_left_child_valid = self.node_exists(self.children(i).next().unwrap());
            if !is_left_child_valid {
                continue;
            }
            
            let partial: AffineView<DomainId>;

            let cache_key = self.children(i).filter_map(|x| self.get_characteristics(x)).collect_vec();
            let shared = get_scale_offset_shared(&cache_key);

            if cache.contains_key(cache_key.as_slice()) {
                // the exact scenario has occurred before so take that partial sum back from the cache.
                partial = *cache.get(cache_key.as_slice()).unwrap()
                // TODO should be extended to just find factorizations as well. aka it could maybe divided everything by 2. Or offset everything by 1.
            } else if let Some((scale, offset)) = shared {
                // scale and offset are matched so potentially there are other vars in the cache.
               let basic_key = self.children(i).filter_map(|x| self.get_basic_characteristics(x)).collect_vec();
                
                let prime_partial: AffineView<DomainId>;
                
                // There are shared variables but their prime is not yet in the map so we insert that first.
                if !cache.contains_key(basic_key.as_slice()) {
                    let prime_children = self.children(i).filter_map(|x| self.get_domain_id(x)).collect_vec();
                    
                    let lb: i32 = prime_children.iter().map(|x| context.lower_bound(x)).sum();
                    let ub: i32 = prime_children.iter().map(|x| context.upper_bound(x)).sum();
                    pumpkin_assert_simple!(lb <= ub, "Cannot create variables with inconsistent domains, ub < lb for index {i}, lb: {lb} ub: {ub}");

                    prime_partial = context.create_new_integer_variable(lb, ub).scaled(1);
                    cache.insert(basic_key, prime_partial);
                } else {
                    prime_partial = *cache.get(basic_key.as_slice()).unwrap()
                }
                // we have a series of shared variables whose prime exists so we return a scaled version of that base.
                partial = prime_partial.scaled(scale).offset(offset);
                cache.insert(cache_key, partial);
            } else {
                // The worst scenario, there is no shared factor to remove from the variables.
                // In this case we have to create a fully unique partial.
                
                
                let lb: i32 = self.children(i).filter_map(|j| self.get_lower_init(context, j)).sum();
                let ub: i32 = self.children(i).filter_map(|j| self.get_upper_init(context, j)).sum();
                
                pumpkin_assert_simple!(lb <= ub, "Cannot create variables with inconsistent domains, ub < lb for index {i}, lb: {lb} ub: {ub}");

                partial = context.create_new_integer_variable(lb, ub).scaled(1);
                cache.insert(cache_key, partial);
            }
            
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
        // Sanity check on lb and ub. Otherwise raise an inconsistency.
        let root = self.partials[0].unwrap();
        
        if self.c < context.lower_bound(&root) {
            return Err(PropositionalConjunction::from(predicate!(root >= self.c)));
        }
        if self.equality && self.c > context.upper_bound(&root) {
            return Err(PropositionalConjunction::from(predicate!(root <= self.c)));
        }
        dbg!(&self.x.iter().map(|x| x.get_domain_id()).collect_vec(), &self.partials);
        
        Ok(())
    }
}

fn get_scale_offset_shared(key: &Vec<(i32, i32, u32)>) -> Option<(i32, i32)> {
    if key.is_empty() {
        return None;
    }

    let (first_i32, second_i32, _) = key[0];
    let all_match = key.iter().all(|&(a, b, _)| a == first_i32 && b == second_i32);

    if all_match {
        Some((first_i32, second_i32))
    } else {
        None
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


    fn get_domain_id(&self, index: usize) -> Option<DomainId> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(x.get_domain_id()),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(x.get_domain_id())
            }
        }
    }
     
    fn get_characteristics(&self, index: usize) -> Option<(i32, i32, u32)> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some(x.get_determining_props()),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some(x.get_determining_props())
            }
        }
    }

    fn get_basic_characteristics(&self, index: usize) -> Option<(i32, i32, u32)> {
        if index >= self.partials.len() {
            let node = self.x.get(index - self.partials.len());
            match node {
                None => None,
                Some(x) => Some((1, 0, x.get_id())),
            }
        } else {
            let node = self.partials[index];
            match node {
                None => None,
                Some(x) => Some((1, 0, x.get_id()))
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

    /// Returns a lower bound predicate for the variable at index i.
    fn get_pred_upper_init(&self, context: &PropagatorInitialisationContext, index: usize) -> Option<Predicate> {
        if !self.node_exists(index) {
            return None;
        }
        if index >= self.partials.len() {
            Some(predicate!(self.x[index - self.partials.len()] <= context.upper_bound(&self.x[index - self.partials.len()])))
        } else {
            let node = self.partials[index].unwrap();
            Some(predicate!(node <= context.upper_bound(&node)))
        }
    }

    /// Returns the range of child indices for the parent at index.
    fn children(&self, index: usize) -> Range<usize> {
        (index*self.b + 1)..(index*self.b + self.b + 1)
    }
    
    fn initial_constraint(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        let root = &self.partials[0].unwrap();
        // Supplying empty reasons should make these roots? Also this just updates the roots accordingly.
        if context.upper_bound(root) > self.c {
            context.set_upper_bound(&self.partials[0].unwrap(), self.c, PropositionalConjunction::default())?;
        }
        
        if self.equality && context.lower_bound(root) < self.c {
            context.set_lower_bound(&self.partials[0].unwrap(), self.c, PropositionalConjunction::default())?;
        }
        
        Ok(())
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([z,z1, x2, x, y, p].into(), 12, Shuffle::None, 3, false))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        let decision = solver.increase_lower_bound_and_notify(propagator, 1, z1, 2);
        match decision {
            EnqueueDecision::Enqueue => {solver.propagate(propagator).expect("non-empty domain");}
            EnqueueDecision::Skip => {}
        }
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), 7, Shuffle::None, 2, false))
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
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), i32::MAX, Shuffle::None, 2, false))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagatorTotalizer::new([x, y].into(), i32::MIN, Shuffle::None, 2, false))
            .expect("Expected no error to be detected");
    }
}
