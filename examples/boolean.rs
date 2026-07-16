use std::convert::Infallible;

use matchcov::{
    Arm, ConstructorFields, ConstructorOracle, ConstructorSpace, Exhaustiveness, Pattern,
    Reachability, UnreachableReason, analyze,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Head {
    False,
    True,
}

struct BoolOracle;

impl ConstructorOracle<Ty, Head> for BoolOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        _: &Ty,
        seen: &[Head],
    ) -> Result<ConstructorSpace<Head>, Self::Error> {
        Ok(ConstructorSpace::from_finite(
            seen,
            [Head::False, Head::True],
        ))
    }

    fn constructor_fields(
        &mut self,
        _: &Ty,
        _: &Head,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Ok(ConstructorFields::Fields(Vec::new()))
    }
}

fn main() {
    let arms = [
        Arm::new([Pattern::constant(Head::True)]),
        Arm::new([Pattern::constant(Head::False)]),
        Arm::new([Pattern::Wildcard]),
    ];

    let analysis = analyze(&mut BoolOracle, &[Ty::Bool], &arms).expect("valid pattern matrix");

    assert_eq!(
        analysis.arms,
        vec![
            Reachability::Reachable,
            Reachability::Reachable,
            Reachability::Unreachable(UnreachableReason::Pattern),
        ]
    );
    assert_eq!(analysis.exhaustiveness, Exhaustiveness::Exhaustive);

    println!("{analysis:#?}");
}
