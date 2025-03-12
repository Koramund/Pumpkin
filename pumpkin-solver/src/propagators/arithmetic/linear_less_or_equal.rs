use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::{predicate, pumpkin_assert_simple};
use crate::predicates::Predicate;
use crate::variables::DomainId;
use std::ops::Range;
use itertools::Itertools;

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
        // TODO double check this size calculation

        // Note that floating precision may bite us and create a larger tree than necessary.
        let size = (self.b as f64).powf((self.x.len() as f64).powf(1.0/(self.b as f64)).ceil()) as usize - 1;

        // let size = pow(div_ceil(nth_root(self.x.len() as f64, self.b as u32), 1), self.b) - 1;
        // dbg!((self.x.len() as f64).powf(1.0/(self.b as f64)), (self.x.len() as f64).powf(1.0/(self.b as f64)).ceil(), size);
        self.partials = vec![None; size].into_boxed_slice();

        for i in (0..size).rev() {

            // Simply if there does not exist a node on the left side this means the parent node will also not need to be constructed
            // and so it is left as None in the array
            let is_left_child_valid = self.node_exists(self.children(i).next().unwrap());
            // dbg!(self.children(i).next().unwrap(), is_left_child_valid);
            if !is_left_child_valid {
                continue;
            }

            // TODO change the get methods to also return options such that filter maps automatically ignore it :P
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

            // TODO We can optimize by making it such that if the left most child does not exist then we also mark this entry as None.

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

        self.total_num = self.partials.len() + self.x.len();
        //
        // dbg!(self.partials.iter().filter(|x| !x.is_none()).map(|p| context.upper_bound(&p.unwrap())).collect_vec());
        // dbg!(&self.partials);
        // dbg!(self.x);
        // dbg!(self.c);
        
        
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

        
        self.push_upper_bound_down(&mut context)?;
        self.push_lower_bound_down(&mut context)?;
        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        
        self.assert_partials_are_fixed_with_children(&mut context)?;
        Ok(())
    }
}



impl<Var: 'static> LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{

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

    // a series of functions such that I do not need to think about what the value of value I actually references
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

    fn set_lower(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_lower_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_lower_bound(&self.partials[index].unwrap(), bound, reason)?;
        }
        Ok(())
    }

    fn set_upper(&self, context: &mut PropagationContextMut, index: usize, bound: i32, reason: PropositionalConjunction) -> PropagationStatusCP {
        if index >= self.partials.len() {
            context.set_upper_bound(&self.x[index - self.partials.len()], bound, reason)?;
        } else {
            context.set_upper_bound(&self.partials[index].unwrap(), bound, reason)?;
        }
        Ok(())
    }

    fn get_pred_lower(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] >= context.lower_bound(&self.x[index - self.partials.len()]))
        } else {
            let node = self.partials[index].unwrap();
            predicate!(node >= context.lower_bound(&node))
        }
    }

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

    fn get_pred_upper(&self, context: &PropagationContextMut, index: usize) -> Predicate {
        if index >= self.partials.len() {
            predicate!(self.x[index - self.partials.len()] <= context.upper_bound(&self.x[index - self.partials.len()]))
        } else {
            let node = self.partials[index].unwrap();
            predicate!(node <= context.upper_bound(&node))
        }
    }

    /// If there are any out of bounds errors, blame this little guy here.
    fn children(&self, index: usize) -> Range<usize> {
        // (index*self.b + 1)..min(index*self.b + self.b + 1, self.total_num)
        (index*self.b + 1)..(index*self.b + self.b + 1)
    }

    fn parent_index(&self, index: usize) -> usize {
        (index - 1) / self.b
    }

    
    fn assert_partials_are_fixed_with_children(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for i in (0..self.partials.len()).rev() {
            if !self.node_exists(i) {
                continue;
            }
            let lb: i32 = self.children(i).filter_map(|j| self.get_lower(context, j)).sum();
            let ub: i32 = self.children(i).filter_map(|j| self.get_upper(context, j)).sum();
            if lb == ub {
                let lb_p = self.get_lower(context, i).unwrap();
                let ub_p = self.get_upper(context, i).unwrap();
                // 
                // dbg!(self.partials.iter().map(|p| { match p { Some(p) => { context.lower_bound(p) } None => {-1} } }).collect_vec());
                // dbg!(self.partials.iter().map(|p| { match p { Some(p) => { context.upper_bound(p) } None => {-1} } }).collect_vec());
                // 
                // dbg!(self.x.iter().map(|x| context.lower_bound(x)).collect_vec());
                // dbg!(self.x.iter().map(|x| context.upper_bound(x)).collect_vec());
                
                pumpkin_assert_simple!(lb_p == ub_p, "This should not fail lb:{lb_p} ub:{ub_p}. Of children its {lb} {ub}");
            }
        }
        Ok(())
    }

    /// Given a consumption by the leaf nodes, push this information back up to the root node.
    /// Simply each child node stipulates the minimum consumption of the branch.
    fn push_lower_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // this one is rather simple.
        for i in (0..self.partials.len()).rev() {
            if !self.node_exists(i) {
                continue;
            }

            let lb: i32 = self.children(i).filter_map(|j| self.get_lower(context, j)).sum();

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
        // each partial updates the nodes below it. This is because the upperbound of the root node cannot be changed by this type of propagation.

        for i in 0..self.partials.len() {
            if !self.node_exists(i) {
                continue;
            }
            // a propagation is responsible for checking the upperbound of the current node
            // then subtracting the lower bound of the neighbours.
            // this then becomes the new upperbound for the node i
            let total_bound = self.get_upper(context, i).unwrap() - self.children(i).filter_map(|j|self.get_lower(context, j)).sum::<i32>();
            for j in self.children(i) {
                if !self.node_exists(j) {
                    continue;
                }

                let new_bound = total_bound + self.get_lower(context, j).unwrap();
                // dbg!((i,j,total_bound, new_bound, self.children(i).map(|j|self.get_lower(context, j)).collect_vec()), self.children(i));
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
        // each partial updates the nodes below it. This is because the upperbound of the root node cannot be changed by this type of propagation.

        for i in 0..self.partials.len() {
            if !self.node_exists(i) {
                continue;
            }
            // this deals with the concept of mandatory consumption
            // the root node has some lower bound of consumption that must take place.
            // this means that your lower bound = mandatory - maximum of your neighbours
            // it is probably a weak propagation but who knows, could be interesting.

            // a propagation is responsible for checking the upperbound of the current node
            // then subtracting the lower bound of the neighbours.
            // this then becomes the new upperbound for the node i
            let total_bound = self.get_lower(context, i).unwrap() - self.children(i).filter_map(|j|self.get_upper(context, j)).sum::<i32>();
            for j in self.children(i) {
                if !self.node_exists(j) {
                    continue;
                }

                let new_bound = total_bound + self.get_upper(context, j).unwrap();
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
