use std::convert::Infallible;

use matchcov::{
    Arm, Config, ConstructorFields, ConstructorOracle, ConstructorSpace, Exhaustiveness,
    InconclusiveReason, MissingHead, Pattern, Reachability, UnreachableReason, Usefulness, Witness,
    analyze, analyze_with_config, usefulness,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Bool,
    Pair(Box<Ty>, Box<Ty>),
    Word,
    One,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Head {
    False,
    True,
    Pair,
    Word(u8),
    Unit,
    Impossible,
}

#[derive(Default)]
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
            Ty::One => ConstructorSpace::from_finite(seen, [Head::Unit]),
        })
    }

    fn constructor_fields(
        &mut self,
        ty: &Ty,
        constructor: &Head,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Ok(match (ty, constructor) {
            (Ty::Bool, Head::False | Head::True)
            | (Ty::Word, Head::Word(_))
            | (Ty::One, Head::Unit) => ConstructorFields::Fields(Vec::new()),
            (Ty::Pair(left, right), Head::Pair) => {
                ConstructorFields::Fields(vec![(**left).clone(), (**right).clone()])
            }
            _ => ConstructorFields::Impossible,
        })
    }
}

fn constant(head: Head) -> Pattern<Head> {
    Pattern::constant(head)
}

fn pair(left: Pattern<Head>, right: Pattern<Head>) -> Pattern<Head> {
    Pattern::constructor(Head::Pair, [left, right])
}

fn witness_constant(head: Head) -> Witness<Head> {
    Witness::Constructor {
        head,
        arguments: Vec::new(),
    }
}

#[test]
fn single_constructor_product_preserves_a_nested_missing_witness() {
    let pair_of_bools = Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Bool));
    let matrix = vec![
        vec![pair(constant(Head::False), Pattern::Wildcard)],
        vec![pair(constant(Head::True), constant(Head::True))],
    ];

    let result = usefulness(&mut Oracle, &[pair_of_bools], &matrix, &[Pattern::Wildcard]).unwrap();

    assert_eq!(
        result,
        Usefulness::Useful(vec![Witness::Constructor {
            head: Head::Pair,
            arguments: vec![witness_constant(Head::True), witness_constant(Head::False),],
        }])
    );
}

#[test]
fn nested_or_patterns_in_a_matrix_are_not_left_biased() {
    let constructor_first = Pattern::or([
        constant(Head::False),
        Pattern::or([Pattern::Wildcard, constant(Head::True)]),
    ]);
    let wildcard_first = Pattern::or([
        Pattern::or([Pattern::Wildcard, constant(Head::False)]),
        constant(Head::True),
    ]);

    for covering_pattern in [constructor_first, wildcard_first] {
        let result = usefulness(
            &mut Oracle,
            &[Ty::Bool],
            &[vec![covering_pattern]],
            &[Pattern::Wildcard],
        )
        .unwrap();
        assert_eq!(result, Usefulness::Useless);
    }
}

struct PanicOracle;

impl ConstructorOracle<(), Head> for PanicOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        _ty: &(),
        _seen: &[Head],
    ) -> Result<ConstructorSpace<Head>, Self::Error> {
        panic!("a zero-column query must not consult its oracle")
    }

    fn constructor_fields(
        &mut self,
        _ty: &(),
        _constructor: &Head,
    ) -> Result<ConstructorFields<()>, Self::Error> {
        panic!("a zero-column query must not consult its oracle")
    }
}

#[test]
fn zero_column_matrices_obey_the_empty_vector_base_case() {
    let uncovered = usefulness(
        &mut PanicOracle,
        &[] as &[()],
        &[] as &[Vec<Pattern<Head>>],
        &[],
    )
    .unwrap();
    assert_eq!(uncovered, Usefulness::Useful(Vec::new()));

    let covered = usefulness(
        &mut PanicOracle,
        &[] as &[()],
        &[Vec::<Pattern<Head>>::new()],
        &[],
    )
    .unwrap();
    assert_eq!(covered, Usefulness::Useless);
}

#[test]
fn zero_column_analysis_has_one_unit_value_vector() {
    let no_arms = analyze(&mut PanicOracle, &[] as &[()], &[] as &[Arm<Head>]).unwrap();
    assert_eq!(
        no_arms.exhaustiveness,
        Exhaustiveness::NonExhaustive(Vec::new())
    );

    let arms = [Arm::<Head>::new([]), Arm::<Head>::new([])];
    let covered = analyze(&mut PanicOracle, &[] as &[()], &arms).unwrap();
    assert_eq!(
        covered.arms,
        vec![
            Reachability::Reachable,
            Reachability::Unreachable(UnreachableReason::Pattern),
        ]
    );
    assert_eq!(covered.exhaustiveness, Exhaustiveness::Exhaustive);
}

#[test]
fn malformed_constructor_arity_in_an_existing_matrix_is_inconclusive() {
    let pair_of_bools = Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Bool));
    let malformed_matrix = vec![vec![Pattern::constructor(Head::Pair, [Pattern::Wildcard])]];
    let query = [pair(Pattern::Wildcard, Pattern::Wildcard)];

    let result = usefulness(&mut Oracle, &[pair_of_bools], &malformed_matrix, &query).unwrap();

    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::ArityMismatch {
            expected: 2,
            actual: 1,
        })
    );
}

#[derive(Clone, Copy)]
enum BadSpace {
    OmitsSeen,
    AddsUnseen,
    ReturnsSeenAsMissing,
}

struct InconsistentSpaceOracle(BadSpace);

impl ConstructorOracle<(), u8> for InconsistentSpaceOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        _ty: &(),
        _seen: &[u8],
    ) -> Result<ConstructorSpace<u8>, Self::Error> {
        Ok(match self.0 {
            BadSpace::OmitsSeen => ConstructorSpace::Complete {
                constructors: vec![2],
            },
            BadSpace::AddsUnseen => ConstructorSpace::Complete {
                constructors: vec![1, 2],
            },
            BadSpace::ReturnsSeenAsMissing => ConstructorSpace::Incomplete {
                missing: MissingHead::Known(1),
            },
        })
    }

    fn constructor_fields(
        &mut self,
        _ty: &(),
        _constructor: &u8,
    ) -> Result<ConstructorFields<()>, Self::Error> {
        Ok(ConstructorFields::Fields(Vec::new()))
    }
}

#[test]
fn contradictory_constructor_spaces_are_reported_as_oracle_inconsistency() {
    let matrix = [vec![Pattern::constant(1)]];

    for bad_space in [
        BadSpace::OmitsSeen,
        BadSpace::AddsUnseen,
        BadSpace::ReturnsSeenAsMissing,
    ] {
        let result = usefulness(
            &mut InconsistentSpaceOracle(bad_space),
            &[()],
            &matrix,
            &[Pattern::Wildcard],
        )
        .unwrap();
        assert_eq!(
            result,
            Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle)
        );
    }
}

#[test]
fn an_explicit_impossible_constructor_is_useless() {
    let result = usefulness(&mut Oracle, &[Ty::One], &[], &[constant(Head::Impossible)]).unwrap();
    assert_eq!(result, Usefulness::Useless);

    let analysis = analyze(
        &mut Oracle,
        &[Ty::One],
        &[Arm::new([constant(Head::Impossible)])],
    )
    .unwrap();
    assert_eq!(
        analysis.arms,
        vec![Reachability::Unreachable(UnreachableReason::Pattern)]
    );
    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(vec![Witness::Wildcard])
    );
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum UninhabitedTy {
    Root,
    Empty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum UninhabitedHead {
    Live,
    Dead,
}

struct UninhabitedMissingOracle;

impl ConstructorOracle<UninhabitedTy, UninhabitedHead> for UninhabitedMissingOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        ty: &UninhabitedTy,
        _seen: &[UninhabitedHead],
    ) -> Result<ConstructorSpace<UninhabitedHead>, Self::Error> {
        Ok(match ty {
            UninhabitedTy::Root => ConstructorSpace::Incomplete {
                missing: MissingHead::Known(UninhabitedHead::Dead),
            },
            UninhabitedTy::Empty => ConstructorSpace::Empty,
        })
    }

    fn constructor_fields(
        &mut self,
        ty: &UninhabitedTy,
        constructor: &UninhabitedHead,
    ) -> Result<ConstructorFields<UninhabitedTy>, Self::Error> {
        Ok(match (ty, constructor) {
            (UninhabitedTy::Root, UninhabitedHead::Live) => ConstructorFields::Fields(Vec::new()),
            (UninhabitedTy::Root, UninhabitedHead::Dead) => {
                ConstructorFields::Fields(vec![UninhabitedTy::Empty])
            }
            _ => ConstructorFields::Impossible,
        })
    }
}

#[test]
fn a_known_missing_constructor_with_uninhabited_fields_is_inconsistent() {
    let matrix = [vec![Pattern::constant(UninhabitedHead::Live)]];
    let result = usefulness(
        &mut UninhabitedMissingOracle,
        &[UninhabitedTy::Root],
        &matrix,
        &[Pattern::Wildcard],
    )
    .unwrap();

    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle)
    );
}

#[test]
fn every_analysis_query_receives_a_fresh_step_budget() {
    let analysis = analyze_with_config(
        &mut Oracle,
        &[Ty::Bool],
        &[Arm::new([constant(Head::False)])],
        Config {
            max_steps: 3,
            max_depth: 32,
        },
    )
    .unwrap();

    assert_eq!(analysis.arms, vec![Reachability::Reachable]);
    assert_eq!(
        analysis.exhaustiveness,
        Exhaustiveness::NonExhaustive(vec![witness_constant(Head::True)])
    );
}

#[test]
fn multi_column_witnesses_describe_only_an_uncovered_value_vector() {
    let matrix = vec![
        vec![constant(Head::True), Pattern::Wildcard],
        vec![Pattern::Wildcard, constant(Head::True)],
    ];
    let result = usefulness(
        &mut Oracle,
        &[Ty::Bool, Ty::Bool],
        &matrix,
        &[Pattern::Wildcard, Pattern::Wildcard],
    )
    .unwrap();

    assert_eq!(
        result,
        Usefulness::Useful(vec![
            witness_constant(Head::False),
            witness_constant(Head::False),
        ])
    );
}

#[test]
fn open_domain_witness_excludes_every_observed_head_once_in_matrix_order() {
    let matrix = vec![
        vec![Pattern::or([
            constant(Head::Word(2)),
            Pattern::or([constant(Head::Word(1)), constant(Head::Word(2))]),
        ])],
        vec![constant(Head::Word(3))],
    ];
    let result = usefulness(&mut Oracle, &[Ty::Word], &matrix, &[Pattern::Wildcard]).unwrap();

    assert_eq!(
        result,
        Usefulness::Useful(vec![Witness::OtherThan {
            excluded: vec![Head::Word(2), Head::Word(1), Head::Word(3)],
        }])
    );
}

#[test]
fn impossible_rows_do_not_poison_exhaustive_coverage() {
    let analysis = analyze(
        &mut Oracle,
        &[Ty::One],
        &[
            Arm::new([constant(Head::Impossible)]),
            Arm::new([constant(Head::Unit)]),
        ],
    )
    .unwrap();

    assert_eq!(
        analysis.arms,
        vec![
            Reachability::Unreachable(UnreachableReason::Pattern),
            Reachability::Reachable,
        ]
    );
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);
}

#[test]
fn an_uninhabited_known_missing_head_is_inconsistent_even_without_observed_heads() {
    let result = usefulness(
        &mut UninhabitedMissingOracle,
        &[UninhabitedTy::Root],
        &[],
        &[Pattern::Wildcard],
    )
    .unwrap();

    assert_eq!(
        result,
        Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle)
    );
}
