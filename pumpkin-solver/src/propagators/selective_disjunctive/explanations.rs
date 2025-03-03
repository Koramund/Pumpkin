use crate::conjunction;
use crate::predicates::Predicate;
use crate::predicates::PropositionalConjunction;
use crate::propagators::ResourceProfile;
use crate::pumpkin_assert_simple;
use crate::variables::IntegerVariable;

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
