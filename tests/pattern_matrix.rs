use std::convert::Infallible;

use matchcov::{
    ConstructorFields, ConstructorOracle, ConstructorSpace, InconclusiveReason, MatrixError,
    MissingHead, Pattern, PatternMatrix, PatternRow, Usefulness, Witness,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Bool,
    Pair(Box<Ty>, Box<Ty>),
    Word,
    Empty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Head {
    False,
    True,
    Pair,
    Word(u8),
    Other,
    Impossible,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArmData {
    arm_index: usize,
    label: &'static str,
}

struct Oracle;

impl ConstructorOracle<Ty, Head> for Oracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        ty: &Ty,
        seen: &[Head],
    ) -> Result<ConstructorSpace<Head>, Self::Error> {
        Ok(match ty {
            Ty::Bool => ConstructorSpace::from_finite(seen, [Head::False, Head::True]),
            Ty::Pair(_, _) => ConstructorSpace::from_finite(seen, [Head::Pair]),
            Ty::Word => ConstructorSpace::open(),
            Ty::Empty => ConstructorSpace::Empty,
        })
    }

    fn constructor_fields(
        &mut self,
        ty: &Ty,
        constructor: &Head,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Ok(match (ty, constructor) {
            (Ty::Bool, Head::False | Head::True) | (Ty::Word, Head::Word(_)) => {
                ConstructorFields::Fields(Vec::new())
            }
            (Ty::Pair(left, right), Head::Pair) => {
                ConstructorFields::Fields(vec![(**left).clone(), (**right).clone()])
            }
            _ => ConstructorFields::Impossible,
        })
    }
}

struct PanicOracle;

impl ConstructorOracle<Ty, Head> for PanicOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        _ty: &Ty,
        _seen: &[Head],
    ) -> Result<ConstructorSpace<Head>, Self::Error> {
        panic!("an invalid index or zero-column query must not consult its oracle")
    }

    fn constructor_fields(
        &mut self,
        _ty: &Ty,
        _constructor: &Head,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        panic!("an invalid index or zero-column query must not consult its oracle")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LookupFailed;

struct FailingOracle;

impl ConstructorOracle<Ty, Head> for FailingOracle {
    type Error = LookupFailed;

    fn constructor_space(
        &mut self,
        _ty: &Ty,
        _seen: &[Head],
    ) -> Result<ConstructorSpace<Head>, Self::Error> {
        Err(LookupFailed)
    }

    fn constructor_fields(
        &mut self,
        _ty: &Ty,
        _constructor: &Head,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Err(LookupFailed)
    }
}

fn pair_ty(left: Ty, right: Ty) -> Ty {
    Ty::Pair(Box::new(left), Box::new(right))
}

fn constant(head: Head) -> Pattern<Head> {
    Pattern::constant(head)
}

fn pair(left: Pattern<Head>, right: Pattern<Head>) -> Pattern<Head> {
    Pattern::constructor(Head::Pair, [left, right])
}

fn row(
    patterns: impl IntoIterator<Item = Pattern<Head>>,
    arm_index: usize,
) -> PatternRow<Head, ArmData> {
    PatternRow::new(
        patterns,
        ArmData {
            arm_index,
            label: match arm_index {
                0 => "zero",
                1 => "one",
                2 => "two",
                3 => "three",
                _ => "other",
            },
        },
    )
}

fn matrix(
    column_types: impl IntoIterator<Item = Ty>,
    rows: impl IntoIterator<Item = PatternRow<Head, ArmData>>,
) -> PatternMatrix<Ty, Head, ArmData> {
    PatternMatrix::new(column_types, rows).unwrap()
}

fn witness_constant(head: Head) -> Witness<Head> {
    Witness::Constructor {
        head,
        arguments: Vec::new(),
    }
}

#[test]
fn wildcard_constructor_specialization_updates_types_and_payload() {
    let input = matrix([pair_ty(Ty::Bool, Ty::Word)], [row([Pattern::Wildcard], 2)]);

    let specialized = input.specialize(&mut Oracle, 0, &Head::Pair).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Bool, Ty::Word],
            [row([Pattern::Wildcard, Pattern::Wildcard], 2)],
        )
    );
}

#[test]
fn constructor_specialization_keeps_matching_rows_and_discards_other_heads() {
    let input = matrix(
        [pair_ty(Ty::Bool, Ty::Word)],
        [
            row([pair(constant(Head::True), constant(Head::Word(7)))], 0),
            row([constant(Head::Other)], 1),
            row([pair(Pattern::Wildcard, constant(Head::Word(9)))], 2),
        ],
    );

    let specialized = input.specialize(&mut Oracle, 0, &Head::Pair).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Bool, Ty::Word],
            [
                row([constant(Head::True), constant(Head::Word(7))], 0),
                row([Pattern::Wildcard, constant(Head::Word(9))], 2),
            ],
        )
    );
}

#[test]
fn constructor_specialization_expands_root_or_patterns_in_stable_order() {
    let input = matrix(
        [pair_ty(Ty::Bool, Ty::Bool)],
        [
            row(
                [Pattern::or([
                    pair(constant(Head::False), constant(Head::True)),
                    Pattern::or([
                        constant(Head::Other),
                        pair(Pattern::Wildcard, constant(Head::False)),
                        pair(constant(Head::True), constant(Head::False)),
                    ]),
                ])],
                1,
            ),
            row(
                [pair(
                    Pattern::or([constant(Head::False), constant(Head::True)]),
                    Pattern::Wildcard,
                )],
                2,
            ),
        ],
    );

    let specialized = input.specialize(&mut Oracle, 0, &Head::Pair).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Bool, Ty::Bool],
            [
                row([constant(Head::False), constant(Head::True)], 1),
                row([Pattern::Wildcard, constant(Head::False)], 1),
                row([constant(Head::True), constant(Head::False)], 1),
                row(
                    [
                        Pattern::or([constant(Head::False), constant(Head::True)]),
                        Pattern::Wildcard,
                    ],
                    2,
                ),
            ],
        )
    );
}

#[test]
fn constructor_specialization_gives_one_wildcard_row_for_alternatives_that_cover_it() {
    let input = matrix(
        [pair_ty(Ty::Bool, Ty::Bool)],
        [
            row(
                [Pattern::or([
                    pair(constant(Head::True), Pattern::Wildcard),
                    pair(
                        Pattern::Wildcard,
                        Pattern::or([constant(Head::False), Pattern::Wildcard]),
                    ),
                    pair(constant(Head::False), constant(Head::False)),
                ])],
                0,
            ),
            row([Pattern::or([Pattern::Wildcard, Pattern::Wildcard])], 1),
            row(
                [Pattern::or([
                    pair(constant(Head::True), Pattern::Wildcard),
                    pair(constant(Head::False), constant(Head::False)),
                ])],
                2,
            ),
        ],
    );

    let specialized = input.specialize(&mut Oracle, 0, &Head::Pair).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Bool, Ty::Bool],
            [
                row([Pattern::Wildcard, Pattern::Wildcard], 0),
                row([Pattern::Wildcard, Pattern::Wildcard], 1),
                row([constant(Head::True), Pattern::Wildcard], 2),
                row([constant(Head::False), constant(Head::False)], 2),
            ],
        )
    );
}

#[test]
fn default_specialization_filters_a_nonzero_column_and_keeps_or_rows_once() {
    let input = matrix(
        [Ty::Word, Ty::Bool, Ty::Word],
        [
            row(
                [
                    constant(Head::Word(0)),
                    constant(Head::False),
                    constant(Head::Word(10)),
                ],
                0,
            ),
            row(
                [
                    constant(Head::Word(1)),
                    Pattern::Wildcard,
                    constant(Head::Word(11)),
                ],
                1,
            ),
            row(
                [
                    constant(Head::Word(2)),
                    Pattern::or([
                        constant(Head::True),
                        Pattern::Wildcard,
                        Pattern::or([Pattern::Wildcard, constant(Head::False)]),
                    ]),
                    constant(Head::Word(12)),
                ],
                2,
            ),
        ],
    );

    let specialized = input.specialize_default(1).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Word, Ty::Word],
            [
                row([constant(Head::Word(1)), constant(Head::Word(11))], 1,),
                row([constant(Head::Word(2)), constant(Head::Word(12))], 2,),
            ],
        )
    );
}

#[test]
fn nonzero_constructor_specialization_splices_patterns_and_types_in_place() {
    let input = matrix(
        [Ty::Word, pair_ty(Ty::Bool, Ty::Word), Ty::Bool],
        [row(
            [
                constant(Head::Word(0)),
                pair(constant(Head::True), constant(Head::Word(1))),
                constant(Head::False),
            ],
            3,
        )],
    );

    let specialized = input.specialize(&mut Oracle, 1, &Head::Pair).unwrap();

    assert_eq!(
        specialized,
        matrix(
            [Ty::Word, Ty::Bool, Ty::Word, Ty::Bool],
            [row(
                [
                    constant(Head::Word(0)),
                    constant(Head::True),
                    constant(Head::Word(1)),
                    constant(Head::False),
                ],
                3,
            )],
        )
    );
}

#[test]
fn swapping_and_removing_columns_keep_types_patterns_and_payloads_aligned() {
    let input = matrix(
        [Ty::Bool, Ty::Word, pair_ty(Ty::Bool, Ty::Word)],
        [
            row(
                [
                    constant(Head::False),
                    constant(Head::Word(1)),
                    pair(constant(Head::True), Pattern::Wildcard),
                ],
                0,
            ),
            row(
                [
                    Pattern::Wildcard,
                    Pattern::or([constant(Head::Word(2)), Pattern::Wildcard]),
                    Pattern::Wildcard,
                ],
                1,
            ),
        ],
    );

    let removed = input.without_column(1).unwrap();
    assert_eq!(
        removed,
        matrix(
            [Ty::Bool, pair_ty(Ty::Bool, Ty::Word)],
            [
                row(
                    [
                        constant(Head::False),
                        pair(constant(Head::True), Pattern::Wildcard),
                    ],
                    0,
                ),
                row([Pattern::Wildcard, Pattern::Wildcard], 1),
            ],
        )
    );

    let mut swapped = input;
    swapped.swap_columns(0, 2).unwrap();
    assert_eq!(
        swapped,
        matrix(
            [pair_ty(Ty::Bool, Ty::Word), Ty::Word, Ty::Bool],
            [
                row(
                    [
                        pair(constant(Head::True), Pattern::Wildcard),
                        constant(Head::Word(1)),
                        constant(Head::False),
                    ],
                    0,
                ),
                row(
                    [
                        Pattern::Wildcard,
                        Pattern::or([constant(Head::Word(2)), Pattern::Wildcard]),
                        Pattern::Wildcard,
                    ],
                    1,
                ),
            ],
        )
    );
}

#[test]
fn matrix_construction_rejects_inconsistent_row_widths() {
    let error = PatternMatrix::new(
        [Ty::Bool, Ty::Word],
        [
            row([Pattern::Wildcard, Pattern::Wildcard], 0),
            row([Pattern::Wildcard], 1),
        ],
    )
    .unwrap_err();

    assert_eq!(
        error,
        MatrixError::RowWidth {
            row: 1,
            expected: 2,
            actual: 1,
        }
    );

    let zero_width_error =
        PatternMatrix::<Ty, Head, ArmData>::new([], [row([Pattern::Wildcard], 0)]).unwrap_err();
    assert_eq!(
        zero_width_error,
        MatrixError::RowWidth {
            row: 0,
            expected: 0,
            actual: 1,
        }
    );
}

#[test]
fn invalid_indexes_are_errors_before_oracle_calls_and_swap_is_atomic() {
    let mut input = matrix(
        [Ty::Bool, Ty::Word],
        [row([Pattern::Wildcard, Pattern::Wildcard], 0)],
    );
    let original = input.clone();
    let bad_column = MatrixError::ColumnOutOfBounds {
        column: 2,
        columns: 2,
    };

    assert_eq!(
        input.specialize(&mut PanicOracle, 2, &Head::Pair),
        Err(bad_column.clone())
    );
    assert_eq!(input.specialize_default(2), Err(bad_column.clone()));
    assert_eq!(input.without_column(2), Err(bad_column.clone()));
    assert_eq!(
        input.column_signature(&mut PanicOracle, 2),
        Err(bad_column.clone())
    );
    assert_eq!(
        input.row_usefulness(&mut PanicOracle, 1),
        Err(MatrixError::RowOutOfBounds { row: 1, rows: 1 })
    );

    assert_eq!(input.swap_columns(0, 2), Err(bad_column.clone()));
    assert_eq!(input, original);
    assert_eq!(input.swap_columns(2, 0), Err(bad_column));
    assert_eq!(input, original);
    assert_eq!(input.swap_columns(1, 1), Ok(()));
    assert_eq!(input, original);
}

#[test]
fn empty_matrices_support_specialization_default_removal_and_signatures() {
    let input = matrix(
        [pair_ty(Ty::Bool, Ty::Word)],
        Vec::<PatternRow<Head, ArmData>>::new(),
    );

    assert_eq!(
        input.specialize(&mut Oracle, 0, &Head::Pair).unwrap(),
        matrix(
            [Ty::Bool, Ty::Word],
            Vec::<PatternRow<Head, ArmData>>::new()
        )
    );
    assert_eq!(
        input.specialize_default(0).unwrap(),
        matrix([], Vec::<PatternRow<Head, ArmData>>::new())
    );
    assert_eq!(
        input.without_column(0).unwrap(),
        matrix([], Vec::<PatternRow<Head, ArmData>>::new())
    );
    assert_eq!(
        input.column_signature(&mut Oracle, 0).unwrap(),
        matchcov::ColumnSignature {
            observed: Vec::new(),
            space: ConstructorSpace::Incomplete {
                missing: MissingHead::Known(Head::Pair),
            },
        }
    );
}

#[test]
fn zero_column_matrices_obey_the_empty_vector_base_case() {
    let empty = matrix([], Vec::<PatternRow<Head, ArmData>>::new());
    assert_eq!(empty.width(), 0);
    assert!(empty.is_empty());

    let mut covered = matrix([], [row([], 0), row([], 1)]);
    assert_eq!(
        covered.row_usefulness(&mut PanicOracle, 0).unwrap(),
        Usefulness::Useful(Vec::new())
    );
    assert_eq!(
        covered.row_usefulness(&mut PanicOracle, 1).unwrap(),
        Usefulness::Useless
    );
    assert_eq!(
        covered.swap_columns(0, 0),
        Err(MatrixError::ColumnOutOfBounds {
            column: 0,
            columns: 0,
        })
    );
}

#[test]
fn column_signatures_distinguish_complete_incomplete_and_open_spaces() {
    let complete = matrix(
        [Ty::Bool],
        [
            row(
                [Pattern::or([
                    constant(Head::True),
                    Pattern::or([constant(Head::False), constant(Head::True)]),
                ])],
                0,
            ),
            row([constant(Head::False)], 1),
        ],
    )
    .column_signature(&mut Oracle, 0)
    .unwrap();
    assert_eq!(complete.observed, vec![Head::True, Head::False]);
    assert_eq!(
        complete.space,
        ConstructorSpace::Complete {
            constructors: vec![Head::False, Head::True],
        }
    );

    let incomplete = matrix([Ty::Bool], [row([constant(Head::True)], 0)])
        .column_signature(&mut Oracle, 0)
        .unwrap();
    assert_eq!(incomplete.observed, vec![Head::True]);
    assert_eq!(
        incomplete.space,
        ConstructorSpace::Incomplete {
            missing: MissingHead::Known(Head::False),
        }
    );

    let open = matrix(
        [Ty::Word],
        [
            row(
                [Pattern::or([
                    constant(Head::Word(2)),
                    Pattern::or([constant(Head::Word(1)), constant(Head::Word(2))]),
                ])],
                0,
            ),
            row([constant(Head::Word(3))], 1),
        ],
    )
    .column_signature(&mut Oracle, 0)
    .unwrap();
    assert_eq!(
        open.observed,
        vec![Head::Word(2), Head::Word(1), Head::Word(3)]
    );
    assert_eq!(
        open.space,
        ConstructorSpace::Incomplete {
            missing: MissingHead::Other,
        }
    );

    let nested_arguments = matrix(
        [pair_ty(Ty::Bool, Ty::Bool)],
        [row([pair(constant(Head::False), constant(Head::True))], 0)],
    )
    .column_signature(&mut Oracle, 0)
    .unwrap();
    assert_eq!(nested_arguments.observed, vec![Head::Pair]);
}

#[test]
fn empty_constructor_space_is_reported_and_has_no_useful_rows() {
    let input = matrix([Ty::Empty], [row([Pattern::Wildcard], 0)]);

    assert_eq!(
        input.column_signature(&mut Oracle, 0).unwrap(),
        matchcov::ColumnSignature {
            observed: Vec::new(),
            space: ConstructorSpace::Empty,
        }
    );
    assert_eq!(
        input.row_usefulness(&mut Oracle, 0).unwrap(),
        Usefulness::Useless
    );
}

#[test]
fn row_usefulness_compares_each_row_only_with_its_predecessors() {
    let input = matrix(
        [Ty::Bool],
        [
            row([constant(Head::False)], 0),
            row([Pattern::Wildcard], 1),
            row([constant(Head::True)], 2),
        ],
    );

    assert_eq!(
        input.row_usefulness(&mut Oracle, 0).unwrap(),
        Usefulness::Useful(vec![witness_constant(Head::False)])
    );
    assert_eq!(
        input.row_usefulness(&mut Oracle, 1).unwrap(),
        Usefulness::Useful(vec![witness_constant(Head::True)])
    );
    assert_eq!(
        input.row_usefulness(&mut Oracle, 2).unwrap(),
        Usefulness::Useless
    );
}

#[test]
fn matching_constructor_arity_mismatches_are_errors_but_other_heads_are_ignored() {
    let malformed = Pattern::constructor(Head::Pair, [Pattern::Wildcard]);
    let input = matrix(
        [pair_ty(Ty::Bool, Ty::Word)],
        [row(
            [Pattern::or([
                pair(Pattern::Wildcard, Pattern::Wildcard),
                malformed,
            ])],
            0,
        )],
    );

    assert_eq!(
        input.specialize(&mut Oracle, 0, &Head::Pair),
        Err(MatrixError::ArityMismatch {
            expected: 2,
            actual: 1,
        })
    );

    let malformed_other_head = matrix(
        [pair_ty(Ty::Bool, Ty::Word)],
        [row(
            [Pattern::constructor(
                Head::Other,
                [Pattern::Wildcard, Pattern::Wildcard, Pattern::Wildcard],
            )],
            0,
        )],
    );
    let specialized = malformed_other_head
        .specialize(&mut Oracle, 0, &Head::Pair)
        .unwrap();
    assert_eq!(specialized.column_types(), &[Ty::Bool, Ty::Word]);
    assert!(specialized.rows().is_empty());
}

#[test]
fn impossible_specialization_removes_the_selected_column_and_all_rows() {
    let input = matrix(
        [Ty::Word, Ty::Bool, Ty::Word],
        [
            row(
                [
                    constant(Head::Word(1)),
                    Pattern::Wildcard,
                    constant(Head::Word(2)),
                ],
                0,
            ),
            row(
                [
                    Pattern::Wildcard,
                    Pattern::constructor(Head::Impossible, [Pattern::Wildcard]),
                    Pattern::Wildcard,
                ],
                1,
            ),
        ],
    );

    let specialized = input.specialize(&mut Oracle, 1, &Head::Impossible).unwrap();

    assert_eq!(specialized.column_types(), &[Ty::Word, Ty::Word]);
    assert!(specialized.rows().is_empty());
}

#[test]
fn oracle_failures_use_operation_errors_but_row_usefulness_stays_inconclusive() {
    let input = matrix([Ty::Bool], [row([constant(Head::False)], 0)]);

    assert_eq!(
        input.specialize(&mut FailingOracle, 0, &Head::False),
        Err(MatrixError::Oracle(LookupFailed))
    );
    assert_eq!(
        input.column_signature(&mut FailingOracle, 0),
        Err(MatrixError::Oracle(LookupFailed))
    );
    assert_eq!(
        input.row_usefulness(&mut FailingOracle, 0).unwrap(),
        Usefulness::Inconclusive(InconclusiveReason::Oracle(LookupFailed))
    );
}

#[test]
fn non_clone_payloads_support_operations_that_do_not_duplicate_rows() {
    #[derive(Debug, PartialEq, Eq)]
    struct NonClonePayload(usize);

    let mut input = PatternMatrix::new(
        [Ty::Bool],
        [PatternRow::new([constant(Head::False)], NonClonePayload(7))],
    )
    .unwrap();

    assert_eq!(input.rows()[0].payload(), &NonClonePayload(7));
    assert_eq!(
        input.column_signature(&mut Oracle, 0).unwrap().observed,
        vec![Head::False]
    );
    assert_eq!(
        input.row_usefulness(&mut Oracle, 0).unwrap(),
        Usefulness::Useful(vec![witness_constant(Head::False)])
    );
    input.swap_columns(0, 0).unwrap();
    assert_eq!(input.rows()[0].patterns(), &[constant(Head::False)]);
}
