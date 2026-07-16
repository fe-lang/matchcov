use std::convert::Infallible;

use matchcov::{
    Arm, Config, ConstructorFields, ConstructorOracle, ConstructorSpace, Exhaustiveness, Guard,
    InconclusiveReason, InputError, Pattern, Reachability, UnreachableReason, Usefulness, Witness,
    analyze, analyze_with_config, usefulness, usefulness_with_config,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Bool,
    Pair(Box<Ty>, Box<Ty>),
    Word,
    Empty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ctor {
    False,
    True,
    Pair,
    Word(u8),
}

#[derive(Default)]
struct TestOracle;

impl ConstructorOracle<Ty, Ctor> for TestOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        ty: &Ty,
        seen: &[Ctor],
    ) -> Result<ConstructorSpace<Ctor>, Self::Error> {
        let space = match ty {
            Ty::Bool => ConstructorSpace::from_finite(seen, [Ctor::False, Ctor::True]),
            Ty::Pair(_, _) => ConstructorSpace::from_finite(seen, [Ctor::Pair]),
            Ty::Word => ConstructorSpace::open(),
            Ty::Empty => ConstructorSpace::Empty,
        };
        Ok(space)
    }

    fn constructor_fields(
        &mut self,
        ty: &Ty,
        constructor: &Ctor,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        let fields = match (ty, constructor) {
            (Ty::Bool, Ctor::False | Ctor::True) | (Ty::Word, Ctor::Word(_)) => {
                ConstructorFields::Fields(Vec::new())
            }
            (Ty::Pair(lhs, rhs), Ctor::Pair) => {
                ConstructorFields::Fields(vec![(**lhs).clone(), (**rhs).clone()])
            }
            _ => ConstructorFields::Impossible,
        };
        Ok(fields)
    }
}

fn constant(head: Ctor) -> Pattern<Ctor> {
    Pattern::constant(head)
}

fn pair(lhs: Pattern<Ctor>, rhs: Pattern<Ctor>) -> Pattern<Ctor> {
    Pattern::constructor(Ctor::Pair, [lhs, rhs])
}

fn witness_constant(head: Ctor) -> Witness<Ctor> {
    Witness::Constructor {
        head,
        arguments: Vec::new(),
    }
}

#[test]
fn exhaustive_boolean_has_no_missing_witness() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[
            Arm::new([constant(Ctor::False)]),
            Arm::new([constant(Ctor::True)]),
        ],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![Reachability::Reachable, Reachability::Reachable]
    );
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
}

#[test]
fn missing_boolean_constructor_is_a_structured_witness() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[Arm::new([constant(Ctor::True)])],
    )
    .unwrap();

    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(vec![witness_constant(Ctor::False)])
    );
}

#[test]
fn wildcard_after_complete_signature_is_unreachable() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[
            Arm::new([constant(Ctor::False)]),
            Arm::new([constant(Ctor::True)]),
            Arm::new([Pattern::Wildcard]),
        ],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![
            Reachability::Reachable,
            Reachability::Reachable,
            Reachability::Unreachable(UnreachableReason::Pattern),
        ]
    );
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
}

#[test]
fn duplicate_literal_is_unreachable_but_open_domain_is_not_exhausted() {
    let one = constant(Ctor::Word(1));
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Word],
        &[Arm::new([one.clone()]), Arm::new([one])],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![
            Reachability::Reachable,
            Reachability::Unreachable(UnreachableReason::Pattern),
        ]
    );
    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(vec![Witness::OtherThan {
            excluded: vec![Ctor::Word(1)],
        }])
    );
}

#[test]
fn nested_constructor_witness_is_preserved() {
    let ty = Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Word));
    let analysis = analyze(
        &mut TestOracle,
        &[ty],
        &[Arm::new([pair(constant(Ctor::True), Pattern::Wildcard)])],
    )
    .unwrap();

    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(vec![Witness::Constructor {
            head: Ctor::Pair,
            arguments: vec![witness_constant(Ctor::False), Witness::Wildcard],
        }])
    );
}

#[test]
fn or_patterns_are_expanded_on_demand() {
    let both = Pattern::or([constant(Ctor::False), constant(Ctor::True)]);
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[Arm::new([both]), Arm::new([Pattern::Wildcard])],
    )
    .unwrap();

    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
    assert_eq!(
        analysis.arms[1],
        Reachability::Unreachable(UnreachableReason::Pattern)
    );

    let wildcard_or_true = Pattern::or([Pattern::Wildcard, constant(Ctor::True)]);
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[Arm::new([wildcard_or_true])],
    )
    .unwrap();
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
}

#[test]
fn empty_or_pattern_matches_nothing() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[Arm::new([Pattern::Or(Vec::new())])],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![Reachability::Unreachable(UnreachableReason::Pattern)]
    );
    assert!(matches!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(_)
    ));
}

#[test]
fn multiple_scrutinees_use_a_real_pattern_matrix() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool, Ty::Bool],
        &[
            Arm::new([constant(Ctor::True), Pattern::Wildcard]),
            Arm::new([Pattern::Wildcard, constant(Ctor::True)]),
            Arm::new([constant(Ctor::False), constant(Ctor::False)]),
        ],
    )
    .unwrap();

    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
    assert!(
        analysis
            .arms
            .iter()
            .all(|result| *result == Reachability::Reachable)
    );
}

#[test]
fn guards_only_contribute_when_they_always_succeed() {
    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[
            Arm::with_guard([Pattern::Wildcard], Guard::MayFail),
            Arm::new([Pattern::Wildcard]),
            Arm::with_guard([Pattern::Wildcard], Guard::Never),
        ],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![
            Reachability::Reachable,
            Reachability::Reachable,
            Reachability::Unreachable(UnreachableReason::Guard),
        ]
    );
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);

    let only_conditional = analyze(
        &mut TestOracle,
        &[Ty::Bool],
        &[Arm::with_guard([Pattern::Wildcard], Guard::MayFail)],
    )
    .unwrap();
    assert!(matches!(
        only_conditional.exhaustiveness,
        Exhaustiveness::NonExhaustive(_)
    ));
}

#[test]
fn empty_types_are_exhaustive_without_arms() {
    let analysis = analyze(&mut TestOracle, &[Ty::Empty], &[]).unwrap();
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);

    let analysis = analyze(
        &mut TestOracle,
        &[Ty::Empty],
        &[Arm::new([Pattern::Wildcard])],
    )
    .unwrap();
    assert_eq!(
        analysis.arms,
        vec![Reachability::Unreachable(UnreachableReason::Pattern)]
    );
}

#[test]
fn malformed_matrix_width_is_rejected_before_analysis() {
    let error = analyze(
        &mut TestOracle,
        &[Ty::Bool, Ty::Bool],
        &[Arm::new([Pattern::Wildcard])],
    )
    .unwrap_err();
    assert_eq!(
        error,
        InputError::MatrixRowWidth {
            row: 0,
            expected: 2,
            actual: 1,
        }
    );

    let error = usefulness(
        &mut TestOracle,
        &[Ty::Bool],
        &[],
        &[Pattern::Wildcard, Pattern::Wildcard],
    )
    .unwrap_err();
    assert_eq!(
        error,
        InputError::QueryWidth {
            expected: 1,
            actual: 2,
        }
    );
}

#[test]
fn constructor_arity_mismatch_is_inconclusive() {
    let malformed = Pattern::constructor(Ctor::Pair, [Pattern::Wildcard]);
    let ty = Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Bool));
    let result = usefulness(&mut TestOracle, &[ty], &[], &[malformed]).unwrap();
    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::ArityMismatch {
            expected: 2,
            actual: 1,
        })
    );
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LookupFailed;

struct FailingOracle;

impl ConstructorOracle<Ty, Ctor> for FailingOracle {
    type Error = LookupFailed;

    fn constructor_space(
        &mut self,
        _ty: &Ty,
        _seen: &[Ctor],
    ) -> Result<ConstructorSpace<Ctor>, Self::Error> {
        Err(LookupFailed)
    }

    fn constructor_fields(
        &mut self,
        _ty: &Ty,
        _constructor: &Ctor,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Err(LookupFailed)
    }
}

#[test]
fn oracle_failure_is_not_collapsed_into_exhaustive() {
    let analysis = analyze(&mut FailingOracle, &[Ty::Bool], &[]).unwrap();
    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::Inconclusive(InconclusiveReason::Oracle(LookupFailed))
    );
}

#[test]
fn step_and_depth_limits_are_visible_results() {
    let result = usefulness_with_config(
        &mut TestOracle,
        &[Ty::Bool],
        &[],
        &[Pattern::Wildcard],
        Config {
            max_steps: 0,
            max_depth: 256,
        },
    )
    .unwrap();
    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::StepLimitExceeded { max_steps: 0 })
    );

    let result = usefulness_with_config(
        &mut TestOracle,
        &[Ty::Bool],
        &[],
        &[Pattern::Wildcard],
        Config {
            max_steps: 100,
            max_depth: 0,
        },
    )
    .unwrap();
    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::DepthLimitExceeded { max_depth: 0 })
    );
}

#[test]
fn each_arm_gets_an_independent_step_budget() {
    let expensive = Pattern::or([
        Pattern::or([constant(Ctor::False), constant(Ctor::True)]),
        constant(Ctor::False),
    ]);
    let analysis = analyze_with_config(
        &mut TestOracle,
        &[Ty::Bool],
        &[
            Arm::with_guard([expensive], Guard::MayFail),
            Arm::new([constant(Ctor::False)]),
        ],
        Config {
            max_steps: 2,
            max_depth: 256,
        },
    )
    .unwrap();

    assert!(matches!(
        analysis.arms[0],
        Reachability::Inconclusive(InconclusiveReason::StepLimitExceeded { .. })
    ));
    assert_eq!(analysis.arms[1], Reachability::Reachable);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoolValue {
    False,
    True,
}

fn bool_pattern_matches(pattern: &Pattern<Ctor>, value: BoolValue) -> bool {
    match pattern {
        Pattern::Wildcard => true,
        Pattern::Constructor { head, arguments } => {
            arguments.is_empty()
                && matches!(
                    (head, value),
                    (Ctor::False, BoolValue::False) | (Ctor::True, BoolValue::True)
                )
        }
        Pattern::Or(alternatives) => alternatives
            .iter()
            .any(|alternative| bool_pattern_matches(alternative, value)),
    }
}

fn row_matches(row: &[Pattern<Ctor>], values: [BoolValue; 2]) -> bool {
    row.iter()
        .zip(values)
        .all(|(pattern, value)| bool_pattern_matches(pattern, value))
}

fn witness_matches(witness: &[Witness<Ctor>], values: [BoolValue; 2]) -> bool {
    witness
        .iter()
        .zip(values)
        .all(|(pattern, value)| match pattern {
            Witness::Wildcard => true,
            Witness::Constructor { head, arguments } => {
                arguments.is_empty()
                    && matches!(
                        (head, value),
                        (Ctor::False, BoolValue::False) | (Ctor::True, BoolValue::True)
                    )
            }
            Witness::OtherThan { excluded } => {
                let value_head = match value {
                    BoolValue::False => Ctor::False,
                    BoolValue::True => Ctor::True,
                };
                !excluded.contains(&value_head)
            }
        })
}

#[test]
fn usefulness_matches_brute_force_for_small_boolean_matrices() {
    let patterns = [
        Pattern::Wildcard,
        constant(Ctor::False),
        constant(Ctor::True),
        Pattern::or([constant(Ctor::False), constant(Ctor::True)]),
        Pattern::or([Pattern::Wildcard, constant(Ctor::False)]),
        Pattern::Or(Vec::new()),
    ];
    let rows = patterns
        .iter()
        .flat_map(|left| {
            patterns
                .iter()
                .map(move |right| vec![left.clone(), right.clone()])
        })
        .collect::<Vec<_>>();
    let values = [
        [BoolValue::False, BoolValue::False],
        [BoolValue::False, BoolValue::True],
        [BoolValue::True, BoolValue::False],
        [BoolValue::True, BoolValue::True],
    ];

    let mut matrices = vec![Vec::new()];
    matrices.extend(rows.iter().cloned().map(|row| vec![row]));
    matrices.extend(rows.iter().flat_map(|first| {
        rows.iter()
            .map(move |second| vec![first.clone(), second.clone()])
    }));

    for matrix in matrices {
        for query in &rows {
            let expected = values.iter().copied().any(|value| {
                row_matches(query, value) && !matrix.iter().any(|row| row_matches(row, value))
            });
            let actual =
                usefulness(&mut TestOracle, &[Ty::Bool, Ty::Bool], &matrix, query).unwrap();

            match actual {
                Usefulness::Useful(witness) => {
                    assert!(expected, "unexpected useful result: {matrix:?} / {query:?}");
                    let represented = values
                        .iter()
                        .copied()
                        .filter(|value| witness_matches(&witness, *value))
                        .collect::<Vec<_>>();
                    assert!(!represented.is_empty(), "uninhabited witness: {witness:?}");
                    assert!(represented.iter().copied().all(|value| {
                        row_matches(query, value)
                            && !matrix.iter().any(|row| row_matches(row, value))
                    }));
                }
                Usefulness::Useless => {
                    assert!(
                        !expected,
                        "unexpected useless result: {matrix:?} / {query:?}"
                    );
                }
                Usefulness::Inconclusive(reason) => {
                    panic!("unexpected inconclusive result: {reason:?}")
                }
            }
        }
    }
}
