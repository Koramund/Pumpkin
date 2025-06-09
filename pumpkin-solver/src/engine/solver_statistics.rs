use crate::basic_types::moving_averages::CumulativeMovingAverage;
use crate::create_statistics_struct;

create_statistics_struct!(
    /// Structure responsible for storing several statistics of the solving process of the
    /// [`ConstraintSatisfactionSolver`].
    SolverStatistics {
        /// Core statistics of the solver engine (e.g. the number of decisions)
        engine_statistics: EngineStatistics,
        /// The statistics related to clause learning
        learned_clause_statistics: LearnedClauseStatistics
    }
);

create_statistics_struct!(
    /// Core statistics of the solver engine (e.g. the number of decisions)
    EngineStatistics {
        /// The number of decisions taken by the solver
        num_decisions: u64,
        /// The number of conflicts encountered by the solver
        num_conflicts: u64,
        /// The number of times the solver has restarted
        num_restarts: u64,
        /// The average number of (integer) propagations made by the solver
        num_propagations: u64,
        /// The amount of time which is spent in the solver
        time_spent_in_solver: u64,
});

create_statistics_struct!(
    /// The statistics related to clause learning
    LearnedClauseStatistics {
        /// The average number of elements in the conflict explanation
        average_conflict_size: CumulativeMovingAverage<u64>,
        /// The average number of literals removed by recursive minimisation during conflict analysis
        average_number_of_removed_literals_recursive: CumulativeMovingAverage<u64>,
        /// The average number of literals removed by semantic minimisation during conflict analysis
        average_number_of_removed_literals_semantic: CumulativeMovingAverage<u64>,
        /// The number of learned clauses which have a size of 1
        num_unit_clauses_learned: u64,
        /// The average length of the learned clauses
        average_learned_clause_length: CumulativeMovingAverage<u64>,
        /// The average number of levels which have been backtracked by the solver (e.g. when a learned clause is created)
        average_backtrack_amount: CumulativeMovingAverage<u64>,
        /// The average literal-block distance (LBD) metric for newly added learned nogoods
        average_lbd: CumulativeMovingAverage<u64>,
        /// Counts how often propagate is called for GEQ
        secondary_propagations_geq: u64,
        /// Counts how often propagate is called for LTMin
        secondary_propagations_lt: u64,

        /// When the cumulative literal was asserting
        propagations_on_cumulative_literal: u64,
        /// When the cumulative literal was present anywhere in the nogood, including asserting.
        propagations_with_cumulative_literal: u64,
        /// Total number of nogood propagations, to help proportionate how often we propagated with them.
        nogood_propagations: u64,
        /// How often does VSIDS decide on these literals.
        decisions_on_extended: u64,
        /// What is the chance a nogood contains such a literal.
        chance_cumulative_literal_is_in_nogood: CumulativeMovingAverage<u64>,
        /// If a nogood contains a cumulative literal, on average how many literals are present?
        avg_cumulative_literal_per_nogood: CumulativeMovingAverage<u64>,
});
