# matchcov

[![Crates.io](https://img.shields.io/crates/v/matchcov.svg?logo=rust)](https://crates.io/crates/matchcov)

`matchcov` is a Rust library that decouples pattern-match coverage analysis from language implementations. Its goal is to make the usefulness algorithm described in Luc Maranget's [Warnings for pattern matching](http://moscova.inria.fr/~maranget/papers/warn/warn.pdf) reusable across compilers that use the same approach.

This abstraction is practical. The core algorithm requires only a small semantic interface: pattern structure, constructor identity and arity, and whether a constructor family is complete. Language-specific concerns such as HIR, type inference, name resolution, source spans, diagnostic codes, and display names remain in adapters.

This repository is in the early stages of extracting the API. See [`src/lib.rs`](src/lib.rs) for the exact current signatures.

## Abstraction boundary

The library is responsible for:

- constructing pattern matrices and performing constructor/default specialization
- semantically expanding or-patterns
- determining the usefulness (reachability) of each arm
- checking exhaustiveness with wildcard queries
- reconstructing missing-pattern witnesses
- accounting for whether guards contribute to the coverage of subsequent arms
- returning three-way results for budget exhaustion and incomplete input: proved useful, proved useless, or inconclusive

Language adapters are responsible for:

- converting parser/HIR patterns into `Pattern<C>`
- deciding when to treat binding patterns as wildcards
- resolving constructor types, identities, instantiated field types, and complete constructor sets
- defining literal equality and distinguishing finite from infinite constructor spaces
- defining policies for private or hidden constructors, opaque types, and uninhabited types
- classifying guard expressions
- deciding when to exclude malformed or poisoned patterns from analysis
- formatting witnesses in the target language's syntax
- generating source spans, severities, diagnostic codes, notes, and help text

This boundary keeps the coverage engine independent of compiler databases, inference contexts, and diagnostic types.

## Algorithm

Each match arm is represented as a row of patterns, with one column per scrutinee, in a matrix `P`. A new row `q` is useful if some value matches `q` but does not match any row in `P`.

1. If the first column of `q` contains a constructor pattern, specialize `P` and `q` for that constructor, insert the constructor arguments as new columns, and recurse.
2. If the first column is a wildcard and the constructors already present completely cover the type's constructor space, inspect every constructor branch. Otherwise, inspect the default matrix.
3. An or-pattern is useful if any of its alternatives is useful.
4. Even for a query against an empty matrix, the oracle checks whether each column, including constructor fields, has an inhabitant before constructing a witness. This prevents an empty type from being incorrectly reported as non-exhaustive. Once all columns have been consumed, the query is useful if there is no empty row; an empty row means the query is already covered.
5. Arm `i` is unreachable only if it is proved useless relative to the coverage of all preceding arms. A match is non-exhaustive if a wildcard row is useful after all arms have been added.

The implementation does not return only a boolean. It returns `Inconclusive` when the recursion budget is exhausted, constructor metadata is inconsistent, arities do not match, or similar issues arise. Adapters can therefore avoid false-positive diagnostics.

## Public API concepts

The API centers on this small data model:

- `Pattern<C>`
  - `Wildcard`
  - `Constructor { head: C, arguments: Vec<Pattern<C>> }`
  - `Or(Vec<Pattern<C>>)`
- `Arm<C>`: a row containing one pattern per scrutinee together with a `Guard`
- `Guard::{Always, MayFail, Never}`: a classification of how a guard contributes to coverage, rather than the guard AST itself
- `ConstructorOracle<T, C>`: the adapter contract that provides the constructor family and instantiated fields for a column type `T`
- `ConstructorFields<T>::Fields(...)` / `Impossible`
- `ConstructorSpace<C>`
  - `Empty`: a constructor space with no inhabitants
  - `Complete { constructors }`: all constructor heads in a finite space are known
  - `Incomplete { missing: MissingHead<C> }`: the space is not complete, but the leading element of an uncovered witness can be constructed
- `MissingHead::{Known(C), Other}`
- three-way usefulness result: `Useful(witness)` / `Useless` / `Inconclusive(reason)`
- high-level result: an `Analysis` containing a `Reachability` value for every arm and an `Exhaustiveness` value

`C` is an adapter-owned identifier that the library does not interpret. It can combine enum variant IDs, built-in constructors, and normalized literals in a single type. It does not need to contain display names or source spans.

`MissingHead::Known` and `MissingHead::Other` distinguish a concrete missing constructor in a closed ADT from the remainder outside the previously seen heads in an open domain such as integers or strings. The latter becomes `Witness::OtherThan { excluded }`, so open domains do not need to be modeled as artificial finite sets.

An arm with a guard is still checked to determine whether unconditional preceding coverage makes the arm itself unreachable. However, while the guard can fail, that arm does not contribute coverage for subsequent arms or exhaustiveness. Integrations without guarded arms can pass `Guard::Always`.

## Minimal example

The following conceptual sketch illustrates the role of the API. Consult the current signatures in [`src/lib.rs`](src/lib.rs) for exact details.

```rust,ignore
use std::convert::Infallible;
use matchcov::{
    analyze, Arm, ConstructorFields, ConstructorOracle, ConstructorSpace,
    Exhaustiveness, Pattern, Witness,
};

#[derive(Clone)]
enum Ty { Bool }

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Ctor { False, True }

struct BoolOracle;

impl ConstructorOracle<Ty, Ctor> for BoolOracle {
    type Error = Infallible;

    fn constructor_space(
        &mut self,
        _: &Ty,
        seen: &[Ctor],
    ) -> Result<ConstructorSpace<Ctor>, Self::Error> {
        Ok(ConstructorSpace::from_finite(
            seen,
            [Ctor::False, Ctor::True],
        ))
    }

    fn constructor_fields(
        &mut self,
        _: &Ty,
        _: &Ctor,
    ) -> Result<ConstructorFields<Ty>, Self::Error> {
        Ok(ConstructorFields::Fields(vec![]))
    }
}

let arms = vec![
    Arm::new([Pattern::constant(Ctor::False)]),
];

let report = analyze(&mut BoolOracle, &[Ty::Bool], &arms)?;

assert!(matches!(
    report.exhaustiveness,
    Exhaustiveness::NonExhaustive(ref row)
        if matches!(row.as_slice(), [Witness::Constructor {
            head: Ctor::True,
            arguments,
        }] if arguments.is_empty())
));
```

A real adapter would display the `Ctor::True` witness as `true` in the target language and attach a non-exhaustive diagnostic to the match expression's source span.

Importantly, `analyze` does not generate diagnostics. Compiler integrations convert its semantic results into their native diagnostic types.

## Separating diagnostics

The library returns semantic facts. For example, it reports only that arm 3 is `Unreachable(Pattern)`, that a missing witness is `Some(false)`, or that analysis ended with `Inconclusive(StepLimitExceeded { .. })`.

The adapter adds source-level context to these facts. This includes the arm and match spans, whether a diagnostic is an error or a warning, its error code, qualified constructor names, abbreviated displays for multiple witnesses, and suppression in the presence of existing type errors. This separation lets each compiler preserve its native diagnostic behavior and user experience.

## Current scope and limitations

Naturally supported:

- wildcard and binding patterns
- finite ADTs, booleans, unit, tuples, and other product types
- nested constructor patterns
- or-patterns
- pattern rows with multiple scrutinees
- literals over open domains, using conservative remainder witnesses

Features that require an additional constructor algebra or adapter policy:

- integer and character range patterns with overlapping intervals
- slice and array patterns, variable lengths, and rest patterns
- GADTs, existentials, and refinement types with context-sensitive constructor availability
- inhabitedness checks that account for uninhabited fields
- external visibility rules for private or hidden constructors and features equivalent to `#[non_exhaustive]`
- view patterns, active patterns, and regex patterns
- determining the truth of arbitrary guard expressions

Expanding range and slice patterns into large numbers of simple constructors would compromise both performance and correctness. These features should instead be designed as dedicated oracle extensions that partition interval or length spaces. For GADTs, constructor availability depends on refinements introduced by other columns, so they require an interface stronger than the current context-free `ConstructorOracle`.
