use std::{error::Error, fmt};

/// The small pattern language consumed by the analysis.
///
/// Bindings are represented by [`Wildcard`](Self::Wildcard). Literals can be
/// represented as language-specific, nullary constructor heads, which keeps
/// equality and canonicalization in the compiler adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<C> {
    /// A wildcard or variable pattern.
    Wildcard,
    /// A constructor and its positional arguments.
    Constructor {
        /// The semantic identity of the constructor.
        head: C,
        /// Constructor arguments in declaration order.
        arguments: Vec<Self>,
    },
    /// Alternatives that match the union of their value sets.
    Or(Vec<Self>),
}

impl<C> Pattern<C> {
    /// Creates a constructor pattern.
    pub fn constructor(head: C, arguments: impl IntoIterator<Item = Self>) -> Self {
        Self::Constructor {
            head,
            arguments: arguments.into_iter().collect(),
        }
    }

    /// Creates a nullary constructor pattern.
    pub fn constant(head: C) -> Self {
        Self::constructor(head, [])
    }

    /// Creates an or-pattern.
    pub fn or(alternatives: impl IntoIterator<Item = Self>) -> Self {
        Self::Or(alternatives.into_iter().collect())
    }
}

/// Whether a match guard is guaranteed to accept its pattern.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Guard {
    /// No guard, or a guard proven to be true.
    #[default]
    Always,
    /// A guard that may reject a value.
    MayFail,
    /// A guard proven to be false.
    Never,
}

/// One match arm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm<C> {
    /// One pattern per scrutinee/column.
    pub patterns: Vec<Pattern<C>>,
    /// The adapter's conservative guard classification.
    pub guard: Guard,
}

impl<C> Arm<C> {
    /// Creates an unguarded arm.
    pub fn new(patterns: impl IntoIterator<Item = Pattern<C>>) -> Self {
        Self {
            patterns: patterns.into_iter().collect(),
            guard: Guard::Always,
        }
    }

    /// Creates an arm with an explicit guard classification.
    pub fn with_guard(patterns: impl IntoIterator<Item = Pattern<C>>, guard: Guard) -> Self {
        Self {
            patterns: patterns.into_iter().collect(),
            guard,
        }
    }
}

/// What the constructor oracle knows about a typed column and its observed
/// constructor heads.
///
/// `Complete` means that `seen` covers every inhabited constructor head of the
/// type; `Incomplete` supplies one missing head or a symbolic missing head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructorSpace<C> {
    /// The type has no values.
    Empty,
    /// The observed heads form a complete signature.
    Complete {
        /// All inhabited heads, in deterministic witness-search order.
        constructors: Vec<C>,
    },
    /// At least one inhabited head is absent from `seen`.
    Incomplete {
        /// A concrete or symbolic missing head.
        missing: MissingHead<C>,
    },
}

impl<C: Clone + Eq> ConstructorSpace<C> {
    /// Classifies a finite, inhabited constructor family against the observed
    /// heads.
    ///
    /// This helper removes duplicate constructors while preserving their first
    /// occurrence. Every supplied constructor must have at least one inhabitant
    /// at the queried type; an adapter that tracks empty fields should filter
    /// impossible heads first.
    pub fn from_finite(seen: &[C], constructors: impl IntoIterator<Item = C>) -> Self {
        let mut constructors = constructors.into_iter().fold(Vec::new(), |mut all, head| {
            if !all.contains(&head) {
                all.push(head);
            }
            all
        });

        if constructors.is_empty() {
            Self::Empty
        } else if let Some(missing) = constructors.iter().find(|head| !seen.contains(head)) {
            Self::Incomplete {
                missing: MissingHead::Known(missing.clone()),
            }
        } else {
            Self::Complete {
                constructors: std::mem::take(&mut constructors),
            }
        }
    }

    /// Describes an open constructor family such as arbitrary integers.
    pub fn open() -> Self {
        Self::Incomplete {
            missing: MissingHead::Other,
        }
    }
}

/// A constructor head known to be absent from the queried matrix column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MissingHead<C> {
    /// A concrete, inhabited constructor that is not in `seen`.
    Known(C),
    /// At least one inhabited constructor other than the observed heads.
    Other,
}

/// The fields of a constructor at a particular scrutinee type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructorFields<T> {
    /// Instantiated field types in declaration order.
    Fields(Vec<T>),
    /// This constructor has no inhabitants at the supplied type.
    Impossible,
}

impl<T> From<Vec<T>> for ConstructorFields<T> {
    fn from(fields: Vec<T>) -> Self {
        Self::Fields(fields)
    }
}

/// Type-dependent facts required by the generic matrix algorithm.
///
/// Methods take `&mut self` so an adapter may normalize inference variables,
/// instantiate generic constructor schemes, or cache database queries. Answers
/// must remain semantically stable within one analysis; mutation must not make
/// the same type/head pair contradict an earlier answer.
pub trait ConstructorOracle<T, C> {
    /// A language-specific lookup or inference failure.
    type Error;

    /// Classifies the constructor family of `ty` relative to `seen`.
    fn constructor_space(&mut self, ty: &T, seen: &[C])
    -> Result<ConstructorSpace<C>, Self::Error>;

    /// Returns the instantiated field types for `constructor` at `ty`.
    fn constructor_fields(
        &mut self,
        ty: &T,
        constructor: &C,
    ) -> Result<ConstructorFields<T>, Self::Error>;
}

/// A structured counterexample produced by the core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Witness<C> {
    /// Any inhabitant of the column type.
    Wildcard,
    /// A concrete constructor witness.
    Constructor {
        /// The semantic constructor identity.
        head: C,
        /// Witnesses for the constructor fields.
        arguments: Vec<Self>,
    },
    /// An inhabited head other than all listed constructors.
    ///
    /// This is useful for open literal domains and hidden/extensible constructor
    /// families. It is a semantic constraint, not necessarily source syntax.
    OtherThan {
        /// Constructor heads excluded by the witness.
        excluded: Vec<C>,
    },
}

/// Why a definite result could not be proven.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InconclusiveReason<E> {
    /// The compiler adapter could not supply a required fact.
    Oracle(E),
    /// The configured recursive-step budget was exhausted.
    StepLimitExceeded {
        /// Configured maximum steps for one usefulness query.
        max_steps: usize,
    },
    /// The configured recursion-depth limit was exhausted.
    DepthLimitExceeded {
        /// Configured maximum recursive depth.
        max_depth: usize,
    },
    /// A pattern supplied a different arity than its constructor type.
    ArityMismatch {
        /// Arity reported by the oracle.
        expected: usize,
        /// Arity present in the pattern.
        actual: usize,
    },
    /// The oracle's constructor-space and field answers contradicted each other.
    InconsistentOracle,
}

/// The result of one usefulness query `U(P, q)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Usefulness<C, E> {
    /// `q` matches at least one value not covered by `P`.
    Useful(Vec<Witness<C>>),
    /// Every value matched by `q` is already covered by `P`, or `q` is empty.
    Useless,
    /// No sound yes/no answer was obtained.
    Inconclusive(InconclusiveReason<E>),
}

/// Why an arm is definitely unreachable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnreachableReason {
    /// Previous unconditional patterns cover the arm.
    Pattern,
    /// The adapter proved that the guard is false.
    Guard,
}

/// Reachability of one match arm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reachability<E> {
    /// The arm can match a value not accepted by prior unconditional arms.
    Reachable,
    /// The arm is definitely unreachable.
    Unreachable(UnreachableReason),
    /// Reachability could not be proven either way.
    Inconclusive(InconclusiveReason<E>),
}

/// Exhaustiveness of the unconditional coverage contributed by the arms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exhaustiveness<C, E> {
    /// Every inhabited value vector is covered.
    Exhaustive,
    /// The contained structured pattern describes a missing value vector.
    NonExhaustive(Vec<Witness<C>>),
    /// Exhaustiveness could not be proven either way.
    Inconclusive(InconclusiveReason<E>),
}

/// Combined arm reachability and match exhaustiveness results.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Analysis<C, E> {
    /// One result for each input arm, in source order.
    pub arms: Vec<Reachability<E>>,
    /// Exhaustiveness after all unconditional arms.
    pub exhaustiveness: Exhaustiveness<C, E>,
}

/// Resource limits applied independently to each usefulness query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    /// Maximum recursive calls per arm or exhaustiveness query.
    pub max_steps: usize,
    /// Maximum recursive call depth.
    pub max_depth: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            max_steps: 16_384,
            max_depth: 256,
        }
    }
}

/// A malformed top-level pattern matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputError {
    /// A matrix row has a different width than the column type vector.
    MatrixRowWidth {
        /// Zero-based row index.
        row: usize,
        /// Number of column types.
        expected: usize,
        /// Number of patterns in the row.
        actual: usize,
    },
    /// The usefulness query has a different width than the column type vector.
    QueryWidth {
        /// Number of column types.
        expected: usize,
        /// Number of patterns in the query.
        actual: usize,
    },
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MatrixRowWidth {
                row,
                expected,
                actual,
            } => write!(
                f,
                "pattern matrix row {row} has width {actual}, expected {expected}"
            ),
            Self::QueryWidth { expected, actual } => {
                write!(f, "query has width {actual}, expected {expected}")
            }
        }
    }
}

impl Error for InputError {}
