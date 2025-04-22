use crate::basic_types::linear_options::{proxy_sort, random_shuffle, Shuffle};
use crate::basic_types::{Inconsistency, PropagationStatusCP};
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::{PropagationContext, Propagator};
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::predicate;
use crate::variables::{AffineView, DomainId, TransformableVariable};
use itertools::Itertools;
use std::cmp::min;
use crate::constraints::{DECOMPOSED, PARTIAL_ENCODINGS};
use crate::propagators::linear_less_or_equal_totalizer::get_scale_offset_shared;

/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagatorSequential<Var> {
    x: Box<[Var]>,
    c: i32,
    equality: bool,

    // Represents the partial sums.
    partials: Box<[AffineView<DomainId>]>,
    m: usize,

    shuffle_strategy: Shuffle,
}

impl<Var> LinearLessOrEqualPropagatorSequential<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32, shuffle_strategy: Shuffle, m: usize, equality: bool) -> Self {
        LinearLessOrEqualPropagatorSequential::<Var> {
            x,
            c,
            equality,
            partials: Box::new([]),
            m,
            shuffle_strategy,
        }
    }
}

impl<Var: 'static> Propagator for LinearLessOrEqualPropagatorSequential<Var>
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
        
        self.update_x_lower_bound(&mut context)?;
        self.update_x_upper_bound(&mut context)?;
        
        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        
        self.push_lower_bound_down(&mut context)?;
        self.push_upper_bound_down(&mut context)?;
        
        Ok(())
    }

    fn priority(&self) -> u32 {
        0
    }

    // This function needs to be altered to create a series of variables a_i
    fn initialise_at_root(&mut self, context: &mut PropagatorInitialisationContext, ) -> Result<(), PropositionalConjunction> {
       
        let mut partials: Vec<AffineView<DomainId>> = Vec::new();

        match self.shuffle_strategy {
            Shuffle::None => {}
            Shuffle::Scalar => {self.x = proxy_sort(&self.x, &self.x.iter().map(|x| x.get_scale()).collect_vec().into_boxed_slice())}
            Shuffle::Random => {self.x = random_shuffle(&self.x, 42)}
        }
        
        let mut cache = PARTIAL_ENCODINGS.lock().unwrap();
        let mut decomp = DECOMPOSED.lock().unwrap();
        
        // Note that this is an invalid key as id 0 belongs to the always true predicate, hence this propagator can never have added it to the map.
        let dummy_key = vec![(-1, -1, 0)];
        if !cache.contains_key(&dummy_key) {
            cache.insert(dummy_key.clone(), context.create_new_integer_variable(0, 0).scaled(1));
        }
        partials.push(*cache.get(&dummy_key).unwrap());
        

        for (i, locality_cluster) in self.x.chunks(self.m).enumerate() {
            
            let cache_key = std::iter::once(partials[i].get_determining_props()).chain(
                locality_cluster.iter().map(|x| x.get_determining_props())
            ).collect_vec();
            
            
            if cache.contains_key(cache_key.as_slice()) {
                partials.push(*cache.get(cache_key.as_slice()).unwrap());
                continue
            }
            
            
            let shared = get_scale_offset_shared(&cache_key);
            if let Some((scale, offset)) = shared {
                
                let basic_key = std::iter::once((1, 0, partials[i].get_id())).chain(
                    locality_cluster.iter().map(|x| (1, 0, x.get_id()))
                ).collect_vec();

                let prime_partial: AffineView<DomainId>;
                if !cache.contains_key(basic_key.as_slice()) {
                    let lb: i32 =  std::iter::once(context.lower_bound(&partials[i].get_domain_id())).chain(locality_cluster.iter().map(|x| context.lower_bound(&x.get_domain_id()))).sum();
                    let ub: i32 =  std::iter::once(context.upper_bound(&partials[i].get_domain_id())).chain(locality_cluster.iter().map(|x| context.upper_bound(&x.get_domain_id()))).sum();
                    prime_partial = context.create_new_integer_variable(lb, ub).scaled(1);
                    cache.insert(basic_key, prime_partial);
                    decomp.insert(prime_partial.get_id(), locality_cluster.iter().map(|x| x.get_id()).chain(std::iter::once(partials[i].get_id())).collect_vec());
                    
                } else {
                    prime_partial = *cache.get(basic_key.as_slice()).unwrap();
                }
                let partial = prime_partial.scaled(scale).offset(offset);
                cache.insert(cache_key, partial);
                partials.push(partial);
                
                continue
            }
            
            
            // No values are in the cache so we built up by hand.
            let lb: i32 =  std::iter::once(context.lower_bound(&partials[i])).chain(locality_cluster.iter().map(|x| context.lower_bound(x))).sum();
            let ub: i32 =  std::iter::once(context.upper_bound(&partials[i])).chain(locality_cluster.iter().map(|x| context.upper_bound(x))).sum();
            
            let partial = context.create_new_integer_variable(lb, ub).scaled(1);

            decomp.insert(partial.get_id(), locality_cluster.iter().map(|x| x.get_id()).chain(std::iter::once(partials[i].get_id())).collect_vec());
            partials.push(partial);
            cache.insert(cache_key, partial);
        }
        
        self.x.iter().enumerate().for_each(|(i, x_i)| {
            let _ = context.register(
                x_i.clone(),
                DomainEvents::BOUNDS,
                LocalId::from(i as u32),
            );
        });
        
        let root = partials.last().unwrap();

        // Error out if the propagator is unfeasible at root.
        if context.lower_bound(root) > self.c {
            return Err(PropositionalConjunction::from(predicate!(root >= self.c+1)));
        }
        if self.equality && context.upper_bound(root) < self.c {
                return Err(PropositionalConjunction::from(predicate!(root <= self.c-1)));
        }
        
        partials.iter().enumerate().for_each(|(i, a_i)| {
            let _ = context.register(a_i.clone(), DomainEvents::BOUNDS, LocalId::from((i + self.x.len()) as u32));
        });
        
        self.partials = partials.iter().map(|x| *x).collect_vec().into();

        Ok(())
    }
}

impl<Var: 'static> LinearLessOrEqualPropagatorSequential<Var>
where
    Var: IntegerVariable,
{

    fn initial_constraint(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        let root = self.partials.last().unwrap();
        // Supplying empty reasons should make these roots? Also this just updates the roots accordingly.
        if context.upper_bound(root) > self.c {
            context.set_upper_bound(root, self.c, PropositionalConjunction::default())?;
        }

        if self.equality && context.lower_bound(root) < self.c {
            context.set_lower_bound(root, self.c, PropositionalConjunction::default())?;
        }

        Ok(())
    }
    
    fn update_x_upper_bound(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // Main loop to update the upper bound of every X based on its local capacity and consumption.
        for i_x in 0..self.x.len() {

            // determine variables shared under the partial
            let l_start = (i_x / self.m) * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            let x_i = &self.x[i_x];
            
            let a_prev = &self.partials[i_x / self.m];
            let a_next = &self.partials[i_x / self.m + 1];

            // Sum all nodes under the partial - the node itself + the lb of the previous partial
            let new_ub: i32 = context.upper_bound(a_next)
                - self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>()
                + context.lower_bound(x_i)
                - context.lower_bound(a_prev);
            
            // detect inconsistencies earlier.
            if context.lower_bound(x_i) > new_ub {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev >= context.lower_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_next <= context.upper_bound(a_next))))
                    .collect();
            
                return Err(Inconsistency::from(reason))
            }

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.upper_bound(x_i) > new_ub {

                // get lower bounds of neighbours
                let reason: PropositionalConjunction = (l_start..l_end)
                    .filter_map(|j| 
                        if j != i_x {
                            Some(predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                        } else { None })
                    .chain(std::iter::once(predicate!(a_prev >= context.lower_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_next <= context.upper_bound(a_next))))
                    .collect();
                
                context.set_upper_bound(x_i, new_ub, reason)?;
            }
        }
        
        Ok(())
    }
    
    fn update_x_lower_bound(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // The LB of an X is based on the mandatory consumption of the next LB
        // And the amount of maximum consumption of its neighbours.

        // Main loop to update the upper bound of every X based on its local capacity and consumption.
        for i_x in 0..self.x.len() {
            
            // determine variables shared under the partial
            let l_start = (i_x / self.m) * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            let x_i = &self.x[i_x];

            let a_prev = &self.partials[i_x / self.m];
            let a_next = &self.partials[i_x / self.m + 1];
            
            // Sum all nodes under the partial - the node itself + the ub of the previous partial
            let mandatory_consumpotion: i32 =
                context.lower_bound(a_next)
                - self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>()
                + context.upper_bound(x_i)
                - context.upper_bound(a_prev);

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.upper_bound(x_i) < mandatory_consumpotion {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev <= context.upper_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_next >= context.lower_bound(a_next))))
                    .collect();
            
                return Err(Inconsistency::from(reason))
            }

            if context.lower_bound(x_i) < mandatory_consumpotion {

                // get lower bounds of neighbours
                let reason: PropositionalConjunction = (l_start..l_end)
                    .filter_map(|j| 
                        if j != i_x {
                            Some(predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                        } else { None })
                    .chain(std::iter::once(predicate!(a_prev <= context.upper_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_next >= context.lower_bound(a_next))))
                    .collect();
                
                context.set_lower_bound(x_i, mandatory_consumpotion, reason)?;
            }
        }
        Ok(())
    }

    fn push_lower_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // We now update the LB of our a to see if any are out of date.
        // It simply checks if all the lower bounds below it summed > the current LB.
        
        // Note the enumerate reset trick here. By slicing the initial array enumerate is an i-1 type var.
        for (i, a_i) in self.partials[1..self.partials.len()].iter().enumerate() {
            let l_start = i * self.m;
            let l_end = min(l_start + self.m, self.x.len());
            let a_prev = &self.partials[i];

            // all nodes before the partial have some UB
            let total_lb = self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>()
                + context.lower_bound(a_prev);

            if total_lb > context.upper_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev >= context.lower_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_i <= context.upper_bound(a_i))))
                    .collect();
            
                return Err(Inconsistency::from(reason))
            }

            if total_lb > context.lower_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev >= context.lower_bound(a_prev))))
                    .collect();
                
                context.set_lower_bound(a_i, total_lb, reason)?
            }
        }
        Ok(())
    }

    fn push_upper_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // We now update the UB of our to see if any are out of date.
        // It simply checks if all the upperbounds below it summed < the current UB.
        for (i, a_i) in self.partials[1..self.partials.len()].iter().enumerate() {
            let l_start = i * self.m;
            let l_end = min(l_start + self.m, self.x.len());
            let a_prev = &self.partials[i];

            // all nodes before the partial have some UB
            let total_ub = self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>()
                + context.upper_bound(a_prev);

            if total_ub < context.lower_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev <= context.upper_bound(a_prev))))
                    .chain(std::iter::once(predicate!(a_i >= context.lower_bound(a_i))))
                    .collect();
            
                return Err(Inconsistency::from(reason))
            }
            
            if total_ub < context.upper_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_prev <= context.upper_bound(a_prev))))
                    .collect();
                
                context.set_upper_bound(a_i, total_ub, reason)?
            }
        }
        Ok(())
    }

    fn push_lower_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials[1..self.partials.len()].iter().enumerate().rev() {
            // Mandatory consumption is not a valid thing to define for the last partial as it has no neighbours.
            // note that due to enumerate this is off by -2 instead of -1
            if i >= self.partials.len() - 2 {
                continue;
            }
            
            let l_start = min((i + 1) * self.m, self.x.len());
            let l_end = min(l_start + self.m, self.x.len());
            let a_next = &self.partials[i+2];

            let mandatory_consumption = context.lower_bound(a_next)
                - self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>();

            if mandatory_consumption > context.upper_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_next >= context.lower_bound(a_next))))
                    .chain(std::iter::once(predicate!(a_i <= context.upper_bound(a_i))))
                    .collect();
            
                return Err(Inconsistency::from(reason))
            }
            
            if mandatory_consumption > context.lower_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_next >= context.lower_bound(a_next))))
                    .collect();
                
                context.set_lower_bound(a_i, mandatory_consumption, reason)?
            }
        }
        Ok(())
    }

    fn push_upper_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials[1..self.partials.len()].iter().enumerate().rev() {
            // note that due to enumerate this is off by -2 instead of -1
            if i >= self.partials.len() - 2 {
                continue;
            }

            let l_start = min((i + 1) * self.m, self.x.len());
            let l_end = min(l_start + self.m, self.x.len());
            let a_next = &self.partials[i+2];

            let remaining_capacity = context.upper_bound(a_next)
                - self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>();

            if remaining_capacity < context.lower_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_next <= context.upper_bound(a_next))))
                    .chain(std::iter::once(predicate!(a_i >= context.lower_bound(a_i))))
                    .collect();

                return Err(Inconsistency::from(reason))
            }
            
            if remaining_capacity < context.upper_bound(a_i) {
                let reason: PropositionalConjunction = (l_start..l_end)
                    .map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                    .chain(std::iter::once(predicate!(a_next <= context.upper_bound(a_next))))
                    .collect();

                context.set_upper_bound(a_i, remaining_capacity, reason)?
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([z,z1, x2, x, y, p].into(), 12, Shuffle::None, 2, false))
            .expect("no empty domains");

        solver.propagate(propagator).expect("non-empty domain");

        solver.increase_lower_bound_and_notify(propagator, 1, z1, 2);

        solver.propagate(propagator).expect("non-empty domain");

        println!("{}", solver.get_reason_int(predicate!(y <= 6)));

        println!("{:?}", solver.reason_store);
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), 7, Shuffle::None, 2, false))
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), i32::MAX, Shuffle::None, 2, false))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), i32::MIN, Shuffle::None, 2, false))
            .expect("Expected no error to be detected");
    }
}
