use std::cmp::Ordering;
use std::rc::Rc;

use itertools::Itertools;
use log::info;

use super::ResourceProfile;
use crate::basic_types::moving_averages::CumulativeMovingAverage;
use crate::basic_types::moving_averages::MovingAverage;
use crate::basic_types::PropagationStatusCP;
use crate::conjunction;
use crate::containers::KeyedVec;
use crate::create_statistics_struct;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::ReadDomains;
use crate::engine::DomainEvents;
use crate::engine::EmptyDomain;
use crate::predicate;
use crate::predicates::Predicate;
use crate::predicates::PropositionalConjunction;
use crate::propagators::util::create_tasks;
use crate::propagators::ArgTask;
use crate::propagators::Task;
use crate::pumpkin_assert_moderate;
use crate::pumpkin_assert_simple;
use crate::statistics::Statistic;
use crate::statistics::StatisticLogger;
use crate::variables::IntegerVariable;
use crate::variables::Literal;

#[derive(Debug, Clone)]
pub(crate) struct BoundDomain {
    lower_bound: i32,
    upper_bound: i32,
    processing_time: u32,
}

impl BoundDomain {
    pub(crate) fn new(lower_bound: i32, upper_bound: i32, processing_time: u32) -> Self {
        Self {
            lower_bound,
            upper_bound,
            processing_time,
        }
    }

    pub(crate) fn get_explanation_for_bound_disjointness<Var: IntegerVariable + 'static>(
        &self,
        self_var: Var,
        other: &Self,
        other_var: Var,
    ) -> PropositionalConjunction {
        pumpkin_assert_simple!(!self.overlaps_with(other));
        if self.upper_bound + self.processing_time as i32 <= other.lower_bound {
            // self ends before other starts
            conjunction!(
                [self_var <= other.lower_bound - self.processing_time as i32]
                    & [other_var >= other.lower_bound]
            )
        } else {
            // other ends before self starts
            pumpkin_assert_simple!(
                other.upper_bound + other.processing_time as i32 <= self.lower_bound
            );
            conjunction!(
                [other_var <= self.lower_bound - other.processing_time as i32]
                    & [self_var >= self.lower_bound]
            )
        }
    }

    pub(crate) fn get_explanation_for_overlap_cumulative<Var: IntegerVariable + 'static>(
        &self,
        self_var: Var,
        other: &Self,
        other_var: Var,
        first_profile: &ResourceProfile<Var>,
        last_profile: &ResourceProfile<Var>,
    ) -> PropositionalConjunction {
        if self.lower_bound > other.lower_bound {
            other.get_explanation_for_overlap_cumulative(
                other_var,
                self,
                self_var,
                first_profile,
                last_profile,
            )
        } else {
            pumpkin_assert_simple!(self.overlaps_with(other));
            pumpkin_assert_simple!(
                self.upper_bound + self.processing_time as i32 > other.lower_bound
            );
            // We know that `self.lower_bound` <= other.lower_bound
            //
            // There are 2 cases:
            // 1. The overlap ends before the end of `other`
            // 2. The overlap ends after the end of `other` (i.e. `self` fully subsumes other)
            if self.upper_bound + self.processing_time as i32
                >= other.upper_bound + other.processing_time as i32
            {
                // We have the case where `self` fully subsumes `other`
                //
                // This can only occur (currently) when performing disjointness mining via the
                // cumulative
                //
                // It does not matter what the value of `self` is and we lift the explanaton of
                // other to be contained in the interval [first_profile.start, last_profile.end]
                pumpkin_assert_simple!(
                    last_profile.end - other.processing_time as i32 + 1 >= other.upper_bound,
                    "{} - {}",
                    last_profile.end - other.processing_time as i32,
                    other.upper_bound
                );
                conjunction!(
                    [other_var >= first_profile.start]
                        & [other_var <= last_profile.end - other.processing_time as i32 + 1]
                )
            } else {
                // We have the case where `self` starts before `other` but ends before `other` ends
                //
                // We lift the explanation such that the overlap is in the interval
                // [first_profile.start, last_profile.end]
                pumpkin_assert_simple!(
                    last_profile.end - self.processing_time as i32 + 1 >= self.upper_bound
                );
                pumpkin_assert_simple!(first_profile.start <= other.lower_bound);
                conjunction!(
                    [self_var <= last_profile.end - self.processing_time as i32 + 1]
                        & [other_var >= first_profile.start]
                )
            }
        }
    }

    pub(crate) fn get_explanation_for_overlap_nogood(
        &self,
        other: &Self,
        self_predicate: Predicate,
        other_predicate: Predicate,
    ) -> PropositionalConjunction {
        pumpkin_assert_simple!(self_predicate.get_domain() != other_predicate.get_domain());
        if self.lower_bound > other.lower_bound {
            other.get_explanation_for_overlap_nogood(self, other_predicate, self_predicate)
        } else {
            pumpkin_assert_simple!(self.overlaps_with(other));
            // We know that `self.lower_bound` <= other.lower_bound
            //
            // There are 2 cases:
            // 1. The overlap ends before the end of `other`
            // 2. The overlap ends after the end of `other` (i.e. `self` fully subsumes other)
            if self.upper_bound + self.processing_time as i32
                >= other.upper_bound + other.processing_time as i32
            {
                // We have the case where `self` fully subsumes `other`
                //
                // This can only occur (currently) when performing disjointness mining via the
                // cumulative
                unreachable!()
            } else {
                // We have the case where `self` starts before `other` but ends before `other` ends
                match (self_predicate, other_predicate) {
                    (
                        Predicate::UpperBound {
                            domain_id,
                            upper_bound,
                        },
                        Predicate::LowerBound {
                            domain_id: other_domain_id,
                            lower_bound,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= upper_bound + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound <= lower_bound - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id >= upper_bound + self.processing_time as i32]
                                & [domain_id <= lower_bound - self.processing_time as i32]
                        )
                    }
                    (
                        Predicate::UpperBound {
                            domain_id,
                            upper_bound,
                        },
                        Predicate::NotEqual {
                            domain_id: other_domain_id,
                            not_equal_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= upper_bound + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound
                                <= not_equal_constant - self.processing_time as i32 + 1
                        );
                        conjunction!(
                            [other_domain_id >= upper_bound + self.processing_time as i32]
                                & [domain_id
                                    <= not_equal_constant - self.processing_time as i32 + 1]
                        )
                    }
                    (
                        Predicate::UpperBound {
                            domain_id,
                            upper_bound,
                        },
                        Predicate::Equal {
                            domain_id: other_domain_id,
                            equality_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= upper_bound + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound <= equality_constant - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id >= upper_bound + self.processing_time as i32]
                                & [domain_id <= equality_constant - self.processing_time as i32]
                        )
                    }
                    (
                        Predicate::NotEqual {
                            domain_id,
                            not_equal_constant,
                        },
                        Predicate::LowerBound {
                            domain_id: other_domain_id,
                            lower_bound,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound
                                >= not_equal_constant + self.processing_time as i32 - 1
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound <= lower_bound - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id
                                >= not_equal_constant + self.processing_time as i32 - 1]
                                & [domain_id <= lower_bound - self.processing_time as i32]
                        )
                    }
                    (
                        Predicate::NotEqual {
                            domain_id,
                            not_equal_constant,
                        },
                        Predicate::NotEqual {
                            domain_id: other_domain_id,
                            not_equal_constant: other_not_equal_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound
                                >= not_equal_constant + self.processing_time as i32 - 1
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound
                                <= other_not_equal_constant - self.processing_time as i32 + 1
                        );
                        conjunction!(
                            [other_domain_id
                                >= not_equal_constant + self.processing_time as i32 - 1]
                                & [domain_id
                                    <= other_not_equal_constant - self.processing_time as i32 + 1]
                        )
                    }
                    (
                        Predicate::NotEqual {
                            domain_id,
                            not_equal_constant,
                        },
                        Predicate::Equal {
                            domain_id: other_domain_id,
                            equality_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound
                                >= not_equal_constant + self.processing_time as i32 - 1
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound <= equality_constant - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id
                                >= not_equal_constant + self.processing_time as i32 - 1]
                                & [domain_id <= equality_constant - self.processing_time as i32]
                        )
                    }
                    (
                        Predicate::Equal {
                            domain_id,
                            equality_constant,
                        },
                        Predicate::LowerBound {
                            domain_id: other_domain_id,
                            lower_bound,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= equality_constant + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound <= lower_bound - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id >= equality_constant + self.processing_time as i32]
                                & [domain_id <= lower_bound - self.processing_time as i32]
                        )
                    }
                    (
                        Predicate::Equal {
                            domain_id,
                            equality_constant,
                        },
                        Predicate::NotEqual {
                            domain_id: other_domain_id,
                            not_equal_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= equality_constant + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound > not_equal_constant - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id >= equality_constant + self.processing_time as i32]
                                & [domain_id
                                    <= not_equal_constant - self.processing_time as i32 + 1]
                        )
                    }
                    (
                        Predicate::Equal {
                            domain_id,
                            equality_constant,
                        },
                        Predicate::Equal {
                            domain_id: other_domain_id,
                            equality_constant: other_equality_constant,
                        },
                    ) => {
                        pumpkin_assert_simple!(
                            other.lower_bound >= equality_constant + self.processing_time as i32
                        );
                        pumpkin_assert_simple!(
                            self.upper_bound
                                >= other_equality_constant - self.processing_time as i32
                        );
                        conjunction!(
                            [other_domain_id >= equality_constant + self.processing_time as i32]
                                & [domain_id
                                    <= other_equality_constant - self.processing_time as i32]
                        )
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    pub(crate) fn apply_predicate(&self, predicate: Predicate) -> Self {
        let mut result = self.clone();
        match predicate {
            Predicate::LowerBound {
                domain_id: _,
                lower_bound,
            } => result.lower_bound = self.lower_bound.max(lower_bound),
            Predicate::UpperBound {
                domain_id: _,
                upper_bound,
            } => result.upper_bound = self.upper_bound.min(upper_bound),
            Predicate::NotEqual {
                domain_id: _,
                not_equal_constant,
            } => {
                if not_equal_constant == self.lower_bound {
                    result.lower_bound += 1
                }
                if not_equal_constant == self.upper_bound {
                    result.upper_bound -= 1
                }
            }
            Predicate::Equal {
                domain_id: _,
                equality_constant,
            } => {
                result.lower_bound = equality_constant;
                result.upper_bound = equality_constant
            }
        }
        result
    }

    pub(crate) fn overlaps_with(&self, other: &Self) -> bool {
        self.lower_bound <= other.upper_bound + other.processing_time as i32
            && other.lower_bound <= self.upper_bound + self.processing_time as i32
    }
}

create_statistics_struct!(NodePackingStatistics {
    n_calls: usize,
    n_conflicts: usize,
    n_trivial_conflicts: usize,
    average_clique_size: CumulativeMovingAverage<usize>,
    average_backjump_height: CumulativeMovingAverage<usize>,

});

pub(crate) struct NodePackingPropagator<Var> {
    parameters: NodePackingParameters<Var>,
    _makespan_variable: Var,
    statistics: NodePackingStatistics,

    remaining: Vec<usize>,
    sorted_intervals_by_decreasing_lct: Vec<(usize, (i32, i32))>,
    intervals: Vec<(i32, i32)>,
}

#[derive(Clone, Debug)]
pub(crate) struct NodePackingParameters<Var> {
    /// The Set of [`Task`]s; for each [`Task`], the [`Task::id`] is assumed to correspond to its
    /// index in this [`Vec`]; this is stored as a [`Box`] of [`Rc`]'s to accomodate the
    /// sharing of the tasks
    pub(crate) tasks: Box<[Rc<Task<Var>>]>,
    /// The capacity of the resource (i.e. how much resource consumption can be maximally
    /// accomodated at each time point)
    pub(crate) disjointness: Vec<Vec<Literal>>,
    pub(crate) mapping: KeyedVec<LocalId, usize>,
}

impl<Var: IntegerVariable + Clone + 'static> NodePackingPropagator<Var> {
    pub(crate) fn new(
        arg_tasks: &[ArgTask<Var>],
        makespan_variable: Var,
        disjointness: Vec<Vec<Literal>>,
    ) -> Self {
        let (tasks, mapping) = create_tasks(arg_tasks);
        let num_tasks = tasks.len();
        let parameters = NodePackingParameters {
            tasks: tasks
                .into_iter()
                .map(Rc::new)
                .collect::<Vec<_>>()
                .into_boxed_slice(),

            disjointness,
            mapping,
        };

        NodePackingPropagator {
            parameters: parameters.clone(),
            _makespan_variable: makespan_variable.clone(),
            statistics: NodePackingStatistics::default(),

            remaining: Vec::with_capacity(num_tasks),
            sorted_intervals_by_decreasing_lct: Vec::with_capacity(num_tasks),
            intervals: Vec::with_capacity(num_tasks),
        }
    }

    fn find_conflict(
        &mut self,
        context: &mut PropagationContextMut<'_>,
    ) -> Result<Option<Vec<usize>>, EmptyDomain> {
        self.intervals.clear();
        self.sorted_intervals_by_decreasing_lct.clear();
        self.parameters
            .tasks
            .iter()
            .enumerate()
            .for_each(|(index, task)| {
                let interval = (
                    context.lower_bound(&task.start_variable),
                    context.upper_bound(&task.start_variable) + task.processing_time,
                );
                self.intervals.push(interval);
                self.sorted_intervals_by_decreasing_lct
                    .push((index, interval));
            });

        // Try finding a conflicting *pair* of tasks
        for (index_lhs, (start_lhs, finish_lhs)) in self.intervals.iter().enumerate() {
            let lhs = &self.parameters.tasks[index_lhs];
            for (index_rhs, (start_rhs, finish_rhs)) in self.intervals.iter().enumerate() {
                if index_rhs == index_lhs {
                    continue;
                }
                let rhs = &self.parameters.tasks[index_rhs];

                if Self::are_disjoint(&self.parameters, context, lhs, rhs, &self.intervals, true)?
                    && lhs.processing_time + rhs.processing_time
                        > finish_rhs.max(finish_lhs) - start_lhs.min(start_rhs)
                {
                    return Ok(Some([index_lhs, index_rhs].to_vec()));
                }
            }
        }
        // We sort the intervals by decreasing lct
        self.sorted_intervals_by_decreasing_lct
            .sort_unstable_by_key(|(_, (_, finish))| -finish);

        for (iter_index, (seed_index, (mut start, mut finish))) in
            self.sorted_intervals_by_decreasing_lct.iter().enumerate()
        {
            self.remaining.clear();
            let mut duration_remaining = 0;
            let mut duration_clique = self.parameters.tasks[*seed_index].processing_time;

            let mut clique = vec![*seed_index];
            self.sorted_intervals_by_decreasing_lct[iter_index + 1..]
                .iter()
                .for_each(|(remaining_index, _)| {
                    duration_remaining += self.parameters.tasks[*remaining_index].processing_time;
                    self.remaining.push(*remaining_index)
                });

            let mut last_selected = &self.parameters.tasks[*seed_index];
            loop {
                // Keep the intervals that not in the clique and can be added to a clique
                //
                // Note that we only need to check whether it is compatible with the currently
                // selected index to be added to the clique since it is necessarily incompatible
                // with all the elements that came before it
                let mut next_ix = None;
                let mut next_value: Option<(i32, i32, i32)> = None;

                self.remaining.retain(|&remaining_ix| {
                    if duration_remaining <= finish - start {
                        // TODO: Better short-circuiting
                        // We will only be removing elements from here on out so we can simply
                        // short-circuit here
                        return false;
                    }
                    let result = !clique.contains(&remaining_ix)
                        && Self::are_disjoint(
                            &self.parameters,
                            context,
                            last_selected,
                            &self.parameters.tasks[remaining_ix],
                            &self.intervals,
                            false,
                        )
                        .expect("Should not be an error here");

                    if !result {
                        duration_remaining -= self.parameters.tasks[remaining_ix].processing_time;
                    } else {
                        // Choose the interval that is not disconnected from [start, finish)
                        // and minimizes the length added to the interval, breaking ties
                        // in favor of intervals with longer durations.
                        let (rem_start, rem_finish) = self.intervals[remaining_ix];
                        if rem_start <= finish && rem_finish >= start {
                            let new_length = finish.max(self.intervals[remaining_ix].1)
                                - start.min(self.intervals[remaining_ix].0);
                            let new_duration = self.parameters.tasks[remaining_ix].processing_time;
                            let new_element = (
                                new_length,
                                -new_duration,
                                -self.parameters.tasks[remaining_ix].resource_usage,
                            );

                            if let Some(element) = next_value.as_mut() {
                                if matches!(new_element.cmp(element), Ordering::Less) {
                                    *element = new_element;
                                    next_ix = Some(remaining_ix);
                                }
                            } else {
                                next_value = Some(new_element);
                                next_ix = Some(remaining_ix);
                            }
                        }
                    }
                    result
                });
                // Short-circuit the search if total remaining duration is not larger
                // than the running time window length
                if duration_remaining <= finish - start {
                    break;
                }
                pumpkin_assert_moderate!(
                    next_ix
                        == self
                            .remaining
                            .iter()
                            .filter(|&&remaining_ix| {
                                let (rem_start, rem_finish) = self.intervals[remaining_ix];
                                if rem_start > finish || rem_finish < start {
                                    return false;
                                }
                                true
                            })
                            .min_by_key(|&&remaining_ix| {
                                let new_length = finish.max(self.intervals[remaining_ix].1)
                                    - start.min(self.intervals[remaining_ix].0);
                                let new_duration =
                                    self.parameters.tasks[remaining_ix].processing_time;
                                (
                                    new_length,
                                    -new_duration,
                                    -self.parameters.tasks[remaining_ix].resource_usage,
                                )
                            })
                            .copied()
                );
                if let Some(next_ix) = next_ix {
                    clique.push(next_ix);
                    start = start.min(self.intervals[next_ix].0);
                    finish = finish.max(self.intervals[next_ix].1);
                    last_selected = &self.parameters.tasks[next_ix];
                    duration_clique += last_selected.processing_time;
                } else {
                    break;
                }
            }
            // Update the best clique if the overflow condition holds
            if duration_clique > finish - start {
                return Ok(Some(clique));
            }
        }
        Ok(None)
    }

    fn are_overlapping(interval_1: (i32, i32), interval_2: (i32, i32)) -> bool {
        interval_1.0 <= interval_2.1 && interval_2.0 <= interval_1.1
    }

    fn are_disjoint(
        parameters: &NodePackingParameters<Var>,
        context: &mut PropagationContextMut<'_>,
        task_lhs: &Rc<Task<Var>>,
        task_rhs: &Rc<Task<Var>>,
        intervals: &[(i32, i32)],
        check_interval: bool,
    ) -> Result<bool, EmptyDomain> {
        let is_literal_true = context.is_literal_true(
            &parameters.disjointness[parameters.mapping[task_lhs.id]]
                [parameters.mapping[task_rhs.id]],
        );
        if !is_literal_true
            && check_interval
            && !Self::are_overlapping(
                intervals[task_lhs.id.unpack() as usize],
                intervals[task_rhs.id.unpack() as usize],
            )
        {
            let domain_self = BoundDomain::new(
                intervals[task_lhs.id.unpack() as usize].0,
                intervals[task_lhs.id.unpack() as usize].1 - task_lhs.processing_time,
                task_lhs.processing_time as u32,
            );
            let domain_other = BoundDomain::new(
                intervals[task_rhs.id.unpack() as usize].0,
                intervals[task_rhs.id.unpack() as usize].1 - task_rhs.processing_time,
                task_rhs.processing_time as u32,
            );

            context.assign_literal(
                &parameters.disjointness[parameters.mapping[task_lhs.id]]
                    [parameters.mapping[task_rhs.id]],
                true,
                domain_self.get_explanation_for_bound_disjointness(
                    task_lhs.start_variable.clone(),
                    &domain_other,
                    task_rhs.start_variable.clone(),
                ),
            )?;
        }
        Ok(is_literal_true)
    }
}

impl<Var: IntegerVariable + 'static> Propagator for NodePackingPropagator<Var> {
    fn name(&self) -> &str {
        "NodePackingPropagator"
    }

    fn log_statistics(&self, statistic_logger: StatisticLogger) {
        self.statistics.log(statistic_logger)
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        self.statistics.n_calls += 1;
        if let Some(clique) = self.find_conflict(&mut context)? {
            self.statistics.n_conflicts += 1;
            if clique.len() == 2 {
                self.statistics.n_trivial_conflicts += 1;
            }
            self.statistics.average_clique_size.add_term(clique.len());

            let (est, lft, sum_of_durations) =
                clique
                    .iter()
                    .fold((i32::MAX, 0, 0), |(est, lft, sum_of_durations), task_ix| {
                        let task = &self.parameters.tasks[*task_ix];
                        (
                            est.min(context.lower_bound(&task.start_variable)),
                            lft.max(
                                context.upper_bound(&task.start_variable) + task.processing_time,
                            ),
                            sum_of_durations + task.processing_time,
                        )
                    });

            pumpkin_assert_simple!(lft - est < sum_of_durations);

            // Based on "Computing Explanations for the Unary Resource Constraint - Petr Vilim"
            let delta = sum_of_durations - (lft - est) - 1;
            let nogood = clique
                .iter()
                .flat_map(|&task_ix| {
                    let task = &self.parameters.tasks[task_ix];
                    [
                        predicate!(
                            task.start_variable >= est - (delta as f64 / 2.0).floor() as i32
                        ),
                        predicate!(
                            task.start_variable
                                <= lft + (delta as f64 / 2.0).ceil() as i32 - task.processing_time
                        ),
                    ]
                })
                .chain(clique.iter().tuple_combinations::<(_, _)>().map(
                    |(&task_lhs_ix, &task_rhs_ix)| {
                        let disjoint = self.parameters.disjointness[task_lhs_ix][task_rhs_ix];
                        predicate!(disjoint == 1)
                    },
                ))
                .collect_vec();
            info!("Found cluster with explanation: {nogood:?}");
            Err(crate::basic_types::Inconsistency::Conflict(
                nogood.into_iter().collect(),
            ))
        } else {
            Ok(())
        }
    }

    fn debug_propagate_from_scratch(&self, _context: PropagationContextMut) -> PropagationStatusCP {
        todo!();
        // if let Some(clique) = self.find_conflict(&mut context)? {
        //    let tasks = self.create_initial_activity_list();
        //    let est = clique
        //        .iter()
        //        .map(|&task_ix| context.lower_bound(&tasks[task_ix].start_variable))
        //        .min()
        //        .expect("Empty clique");
        //    let lft = clique
        //        .iter()
        //        .map(|&task_ix| {
        //            let task = &tasks[task_ix];
        //            context.upper_bound(&task.start_variable) + task.processing_time
        //        })
        //        .max()
        //        .expect("Empty clique");
        //    Err(crate::basic_types::Inconsistency::Conflict(
        //        clique
        //            .iter()
        //            .flat_map(|&task_ix| {
        //                let task = &tasks[task_ix];
        //                [
        //                    predicate!(task.start_variable >= est),
        //                    predicate!(task.start_variable <= lft - task.processing_time),
        //                ]
        //            })
        //            .chain(clique.iter().tuple_combinations::<(_, _)>().map(
        //                |(&task_lhs_ix, &task_rhs_ix)| {
        //                    let disjoint = self.parameters.disjointness[task_lhs_ix][task_rhs_ix];
        //                    predicate!(disjoint == 1)
        //                },
        //            ))
        //            .collect(),
        //    ))
        //} else {
        //    Ok(())
        //}
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        for (index, task) in self.parameters.tasks.iter().enumerate() {
            let _ = context.register(
                task.start_variable.clone(),
                DomainEvents::BOUNDS,
                LocalId::from(index as u32),
            );
        }
        let mut current_index = self.parameters.tasks.len();
        for index in 0..self.parameters.disjointness.len() {
            for other_index in index + 1..self.parameters.disjointness.len() {
                let _ = context.register(
                    self.parameters.disjointness[index][other_index],
                    DomainEvents::BOUNDS,
                    LocalId::from(current_index as u32),
                );
                current_index += 1;
            }
        }
        Ok(())
    }
}
