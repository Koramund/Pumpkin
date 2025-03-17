use crate::basic_types::linear_options::{proxy_sort, random_shuffle, Shuffle};
use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::contexts::StatefulPropagationContext;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::{LocalId, PropagationContextMut};
use crate::engine::variables::IntegerVariable;
use crate::engine::DomainEvents;
use crate::predicate;
use crate::variables::DomainId;
use itertools::Itertools;
use std::cmp::min;


/// Propagator for the constraint `reif => \sum x_i <= c`.
#[derive(Clone, Debug)]
pub(crate) struct LinearLessOrEqualPropagatorSequential<Var> {
    x: Box<[Var]>,
    c: i32,

    // Represents the partial sums.
    partials: Box<[DomainId]>,
    m: usize,

    shuffle_strategy: Shuffle,
}

impl<Var> LinearLessOrEqualPropagatorSequential<Var>
where
    Var: IntegerVariable,
{
    pub(crate) fn new(x: Box<[Var]>, c: i32, shuffle_strategy: Shuffle, m: usize) -> Self {
        LinearLessOrEqualPropagatorSequential::<Var> {
            x,
            c,
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

        self.push_lower_bound_up(&mut context)?;
        self.push_upper_bound_up(&mut context)?;
        self.push_lower_bound_down(&mut context)?;
        self.push_upper_bound_down(&mut context)?;

        self.update_x_lower_bound(&mut context)?;
        self.update_x_upper_bound(&mut context)?;

        Ok(())
    }

    fn priority(&self) -> u32 {
        0
    }

    // This function needs to be altered to create a series of variables a_i
    fn initialise_at_root(&mut self, context: &mut PropagatorInitialisationContext, ) -> Result<(), PropositionalConjunction> {
        let mut lower_bound_left_hand_side = 0_i32;
        let mut upper_bound_left_hand_side = 0_i32;
        let mut partial_lowers: Vec<i32> = Vec::new();
        let mut partial_uppers: Vec<i32> = Vec::new();

        match self.shuffle_strategy {
            Shuffle::None => {}
            Shuffle::Scalar => {self.x = proxy_sort(&self.x, &self.x.iter().map(|x| x.get_scale()).collect_vec().into_boxed_slice())}
            Shuffle::Random => {self.x = random_shuffle(&self.x, 42)}
        }

        self.x.iter().enumerate().for_each(|(i, x_i)| {

            let _ = context.register(
                x_i.clone(),
                DomainEvents::BOUNDS,
                LocalId::from(i as u32),
            );

            // saves the lower bound for the next partial.
            if (i % self.m) == 0 && i > 0 {
                partial_lowers.push(lower_bound_left_hand_side);
                partial_uppers.push(upper_bound_left_hand_side);
            }

            // updates lower bound according to the default variables
            lower_bound_left_hand_side += context.lower_bound(x_i);
            upper_bound_left_hand_side += context.upper_bound(x_i);
        });

        self.partials = partial_lowers.iter().zip(partial_uppers.iter()).map(|(&lower, &upper)| {
            context.create_new_integer_variable(lower, upper)
        }).collect_vec()
            .into();

        self.partials.iter().enumerate().for_each(|(i, a_i)| {
            let _ = context.register(a_i.clone(), DomainEvents::BOUNDS, LocalId::from((i + self.x.len()) as u32));
        });

        Ok(())
    }

    fn detect_inconsistency(
        &self,
        context: StatefulPropagationContext,
    ) -> Option<PropositionalConjunction> {

        let start = self.x.len() - (((self.x.len() - 1) % self.m) + 1);
        let end = self.x.len();

        let lb: i32 = self.x[start..end]
            .iter()
            .map(|var| context.lower_bound(var))
            .sum::<i32>() + if self.partials.len() > 0 {context.lower_bound(&self.partials[self.partials.len()-1])} else {0};

        if lb > self.c {
            let mut reason: PropositionalConjunction = self.x[start..end]
                .iter()
                .map(|var| predicate![var >= context.lower_bound(var)])
                .collect();
            if self.partials.len() > 0 {
                reason.add(predicate!(self.partials[self.partials.len()-1] >= context.lower_bound(&self.partials[self.partials.len()-1])));
            }
            Some(reason)
        } else {
            None
        }
    }
}

impl<Var: 'static> LinearLessOrEqualPropagatorSequential<Var>
where
    Var: IntegerVariable,
{
    fn update_x_upper_bound(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // Main loop to update the upper bound of every X based on its local capacity and consumption.
        for i_x in 0..self.x.len() {

            // determine variables shared under the partial
            let l_start = (i_x / self.m) * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            let x_i = &self.x[i_x];

            // Sum all nodes under the partial - the node itself + the lb of the previous partial
            let surrounding_consumption: i32 = self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>()
                - context.lower_bound(x_i)
                + if i_x >= self.m { context.lower_bound(&self.partials[i_x / self.m - 1]) } else { 0 };

            // The remaining energy is determined by the next partials upper bound as that explains how much energy has been consumed ahead.
            let upperbound = if i_x / self.m < self.partials.len() { context.upper_bound(&self.partials[i_x / self.m]) } else { self.c };
            let bound = upperbound - surrounding_consumption;

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.upper_bound(x_i) > bound {

                // get lower bounds of neighbours
                let mut reason: PropositionalConjunction = (l_start..l_end).filter_map(|j| if j != i_x {
                    Some(predicate!(self.x[j] >= context.lower_bound(&self.x[j])))
                } else { None }).collect();

                // lower bound of previous partial if it exists
                if i_x >= self.m {
                    let a = &self.partials[(i_x / self.m) - 1];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }

                // Upper bound of next partial is required as it determines energy capacity
                if i_x / self.m < self.partials.len() {
                    let a = &self.partials[i_x / self.m];
                    reason.push(predicate!(a <= context.upper_bound(a)))
                }

                context.set_upper_bound(x_i, bound, reason)?;
            }
        }
        
        Ok(())
    }
    
    fn update_x_lower_bound(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // The LB of an X is based on the mandatory consumption of the next LB
        // And the amount of maximum consumption of its neighbours.

        // Main loop to update the upper bound of every X based on its local capacity and consumption.
        for i_x in 0..self.x.len() {

            // Mandatory consumption is not a valid thing to define for the last x variables.
            // As self.c has no direct lower bound we cannot dictate this value.
            if i_x / self.m >= self.partials.len() {
                continue;
            }

            // determine variables shared under the partial
            let l_start = (i_x / self.m) * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            let x_i = &self.x[i_x];

            // Sum all nodes under the partial - the node itself + the ub of the previous partial
            let surrounding_max_consumption: i32 = self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>()
                - context.upper_bound(x_i)
                + if i_x >= self.m { context.upper_bound(&self.partials[i_x / self.m - 1]) } else { 0 };

            // The mandatory consumption is determined by the next partials lower bound as that explains how much energy must be consumed here.
            let mandatory_consumption_a = context.lower_bound(&self.partials[i_x / self.m]);
            let bound = mandatory_consumption_a - surrounding_max_consumption;

            // if the previous capacity of x_i is larger, then we want to lower bound it.
            if context.lower_bound(x_i) < bound {

                // get lower bounds of neighbours
                let mut reason: PropositionalConjunction = (l_start..l_end).filter_map(|j| if j != i_x {
                    Some(predicate!(self.x[j] <= context.upper_bound(&self.x[j])))
                } else { None }).collect();

                // lower bound of previous partial if it exists
                if i_x >= self.m {
                    let a = &self.partials[(i_x / self.m) - 1];
                    reason.push(predicate!(a <= context.upper_bound(a)))
                }

                // Upper bound of next partial is required as it determines energy capacity
                if i_x / self.m < self.partials.len() {
                    let a = &self.partials[i_x / self.m];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }

                context.set_lower_bound(x_i, bound, reason)?;
            }
        }
        Ok(())
    }

    fn push_lower_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // We now update the LB of our a to see if any are out of date.
        // It simply checks if all the lower bounds below it summed > the current LB.
        for (i, a_i) in self.partials.iter().enumerate() {
            let l_start = i * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            // all nodes before the partial have some UB
            let total_lb = self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>()
                + if i > 0 { context.lower_bound(&self.partials[i - 1]) } else { 0 };

            if total_lb > context.lower_bound(a_i) {
                let mut reason: PropositionalConjunction = (l_start..l_end).map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j]))).collect();

                if i > 0 {
                    let a = &self.partials[i - 1];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }
                context.set_lower_bound(a_i, total_lb, reason)?
            }
        }
        Ok(())
    }

    fn push_upper_bound_up(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        // We now update the UB of our to see if any are out of date.
        // It simply checks if all the upperbounds below it summed < the current UB.
        for (i, a_i) in self.partials.iter().enumerate() {
            let l_start = i * self.m;
            let l_end = min(l_start + self.m, self.x.len());

            // all nodes before the partial have some UB
            let total_ub = self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>()
                + if i > 0 { context.upper_bound(&self.partials[i - 1]) } else { 0 };

            if total_ub < context.upper_bound(a_i) {
                let mut reason: PropositionalConjunction = (l_start..l_end).map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j]))).collect();

                if i > 0 {
                    let a = &self.partials[i - 1];
                    reason.push(predicate!(a <= context.upper_bound(a)))
                }
                context.set_upper_bound(a_i, total_ub, reason)?
            }
        }
        Ok(())
    }

    fn push_lower_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials.iter().enumerate().rev() {
            // Mandatory consumption is not a valid thing to define for the last partial
            // As self.c has no direct lower bound we cannot dictate this value.
            if i >= self.partials.len() - 1 {
                continue;
            }
            
            let l_start = min((i + 1) * self.m, self.x.len());
            let l_end = min(l_start + self.m, self.x.len());

            let mandatory_consumption = context.lower_bound(&self.partials[i + 1])
                - self.x[l_start..l_end].iter().map(|x_j| { context.upper_bound(x_j) }).sum::<i32>();

            if mandatory_consumption > context.lower_bound(a_i) {
                let mut reason: PropositionalConjunction = (l_start..l_end).map(|j| predicate!(self.x[j] <= context.upper_bound(&self.x[j]))).collect();
                
                if i < self.partials.len() - 1 {
                    let a = &self.partials[i + 1];
                    reason.push(predicate!(a >= context.lower_bound(a)))
                }
                context.set_lower_bound(a_i, mandatory_consumption, reason)?
            }
        }
        Ok(())
    }

    fn push_upper_bound_down(&self, context: &mut PropagationContextMut) -> PropagationStatusCP {
        for (i, a_i) in self.partials.iter().enumerate().rev() {
            let l_start = min((i + 1) * self.m, self.x.len());
            let l_end = min(l_start + self.m, self.x.len());

            let remaining_capacity = if i < self.partials.len() - 1 {context.upper_bound(&self.partials[i + 1])} else {self.c}
                - self.x[l_start..l_end].iter().map(|x_j| { context.lower_bound(x_j) }).sum::<i32>();

            if remaining_capacity < context.upper_bound(a_i) {
                let mut reason: PropositionalConjunction = (l_start..l_end).map(|j| predicate!(self.x[j] >= context.lower_bound(&self.x[j]))).collect();

                if i < self.partials.len() - 1 {
                    let a = &self.partials[i + 1];
                    reason.push(predicate!(a <= context.upper_bound(a)))
                }
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([z,z1, x2, x, y, p].into(), 12, Shuffle::None, 2))
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), 7, Shuffle::None, 2))
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
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), i32::MAX, Shuffle::None, 2))
            .expect_err("Expected overflow to be detected");
    }

    #[test]
    fn underflow_leads_to_no_propagation() {
        let mut solver = TestSolver::default();

        let x = solver.new_variable(i32::MIN, i32::MIN);
        let y = solver.new_variable(-1, -1);

        let _ = solver
            .new_propagator(LinearLessOrEqualPropagatorSequential::new([x, y].into(), i32::MIN, Shuffle::None, 2))
            .expect("Expected no error to be detected");
    }
}
