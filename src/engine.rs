use crate::{
    Analysis, Arm, Config, ConstructorFields, ConstructorOracle, ConstructorSpace, Exhaustiveness,
    Guard, InconclusiveReason, InputError, MissingHead, Pattern, Reachability, UnreachableReason,
    Usefulness, Witness,
};

/// Analyzes every arm and the final exhaustiveness of a match.
///
/// Only arms whose guard is [`Guard::Always`] contribute coverage to later arms
/// and to the exhaustiveness result. Each usefulness query receives an
/// independent [`Config::max_steps`] budget, so a difficult early arm does not
/// change the status of later, simple arms.
pub fn analyze<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    arms: &[Arm<C>],
) -> Result<Analysis<C, O::Error>, InputError>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    analyze_with_config(oracle, column_types, arms, Config::default())
}

/// Analyzes a match with explicit resource limits.
pub fn analyze_with_config<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    arms: &[Arm<C>],
    config: Config,
) -> Result<Analysis<C, O::Error>, InputError>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    validate_matrix(
        column_types.len(),
        arms.iter().map(|arm| arm.patterns.as_slice()),
    )?;

    let mut coverage = Vec::<Vec<Pattern<C>>>::with_capacity(arms.len());
    let mut reachability = Vec::with_capacity(arms.len());

    for arm in arms {
        let result = if arm.guard == Guard::Never {
            Reachability::Unreachable(UnreachableReason::Guard)
        } else {
            match usefulness_unchecked(oracle, column_types, &coverage, &arm.patterns, config) {
                Usefulness::Useful(_) => Reachability::Reachable,
                Usefulness::Useless => Reachability::Unreachable(UnreachableReason::Pattern),
                Usefulness::Inconclusive(reason) => Reachability::Inconclusive(reason),
            }
        };
        let contributes_coverage =
            arm.guard == Guard::Always && !matches!(result, Reachability::Unreachable(_));
        reachability.push(result);

        // A definitely useless row contributes no values beyond the existing
        // matrix, and an impossible row contributes none at all. Omitting both
        // also prevents invalid/impossible heads from polluting `seen`.
        if contributes_coverage {
            coverage.push(arm.patterns.clone());
        }
    }

    let wildcard_query = vec![Pattern::Wildcard; column_types.len()];
    let exhaustiveness =
        match usefulness_unchecked(oracle, column_types, &coverage, &wildcard_query, config) {
            Usefulness::Useful(witness) => Exhaustiveness::NonExhaustive(witness),
            Usefulness::Useless => Exhaustiveness::Exhaustive,
            Usefulness::Inconclusive(reason) => Exhaustiveness::Inconclusive(reason),
        };

    Ok(Analysis {
        arms: reachability,
        exhaustiveness,
    })
}

/// Computes whether `query` matches a value vector not covered by `matrix`.
pub fn usefulness<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    matrix: &[Vec<Pattern<C>>],
    query: &[Pattern<C>],
) -> Result<Usefulness<C, O::Error>, InputError>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    usefulness_with_config(oracle, column_types, matrix, query, Config::default())
}

/// Computes one usefulness query with explicit resource limits.
pub fn usefulness_with_config<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    matrix: &[Vec<Pattern<C>>],
    query: &[Pattern<C>],
    config: Config,
) -> Result<Usefulness<C, O::Error>, InputError>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    validate_matrix(column_types.len(), matrix.iter().map(Vec::as_slice))?;
    if query.len() != column_types.len() {
        return Err(InputError::QueryWidth {
            expected: column_types.len(),
            actual: query.len(),
        });
    }

    Ok(usefulness_unchecked(
        oracle,
        column_types,
        matrix,
        query,
        config,
    ))
}

fn validate_matrix<'a, C: 'a>(
    expected: usize,
    rows: impl IntoIterator<Item = &'a [Pattern<C>]>,
) -> Result<(), InputError> {
    for (row, patterns) in rows.into_iter().enumerate() {
        if patterns.len() != expected {
            return Err(InputError::MatrixRowWidth {
                row,
                expected,
                actual: patterns.len(),
            });
        }
    }
    Ok(())
}

fn usefulness_unchecked<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    matrix: &[Vec<Pattern<C>>],
    query: &[Pattern<C>],
    config: Config,
) -> Usefulness<C, O::Error>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    let mut budget = Budget::new(config);
    usefulness_rec(oracle, column_types, matrix, query, &mut budget, 0)
}

fn usefulness_rec<T, C, O>(
    oracle: &mut O,
    column_types: &[T],
    matrix: &[Vec<Pattern<C>>],
    query: &[Pattern<C>],
    budget: &mut Budget,
    depth: usize,
) -> Usefulness<C, O::Error>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    if let Err(reason) = budget.enter(depth) {
        return Usefulness::Inconclusive(reason);
    }

    if column_types.is_empty() {
        return if matrix.is_empty() {
            Usefulness::Useful(Vec::new())
        } else {
            Usefulness::Useless
        };
    }

    let (head_ty, rest_types) = column_types
        .split_first()
        .expect("non-empty column types were checked above");
    let (head_query, rest_query) = query
        .split_first()
        .expect("top-level widths and recursive transformations preserve query width");

    match head_query {
        Pattern::Constructor { head, arguments } => {
            let field_types = match oracle.constructor_fields(head_ty, head) {
                Ok(ConstructorFields::Fields(fields)) => fields,
                Ok(ConstructorFields::Impossible) => return Usefulness::Useless,
                Err(error) => {
                    return Usefulness::Inconclusive(InconclusiveReason::Oracle(error));
                }
            };
            if field_types.len() != arguments.len() {
                return Usefulness::Inconclusive(InconclusiveReason::ArityMismatch {
                    expected: field_types.len(),
                    actual: arguments.len(),
                });
            }

            let specialized =
                match specialize_matrix::<_, O::Error>(matrix, head, field_types.len()) {
                    Ok(matrix) => matrix,
                    Err(reason) => return Usefulness::Inconclusive(reason),
                };
            let mut next_types = field_types;
            next_types.extend_from_slice(rest_types);
            let mut next_query = arguments.clone();
            next_query.extend_from_slice(rest_query);

            recompose_constructor(
                head.clone(),
                arguments.len(),
                usefulness_rec(
                    oracle,
                    &next_types,
                    &specialized,
                    &next_query,
                    budget,
                    depth + 1,
                ),
            )
        }
        Pattern::Wildcard => usefulness_wildcard(
            oracle, head_ty, rest_types, matrix, rest_query, budget, depth,
        ),
        Pattern::Or(alternatives) => {
            let mut first_inconclusive = None;
            for alternative in alternatives {
                let mut expanded_query = Vec::with_capacity(query.len());
                expanded_query.push(alternative.clone());
                expanded_query.extend_from_slice(rest_query);
                match usefulness_rec(
                    oracle,
                    column_types,
                    matrix,
                    &expanded_query,
                    budget,
                    depth + 1,
                ) {
                    useful @ Usefulness::Useful(_) => return useful,
                    Usefulness::Useless => {}
                    Usefulness::Inconclusive(reason) => {
                        first_inconclusive.get_or_insert(reason);
                    }
                }
            }
            first_inconclusive.map_or(Usefulness::Useless, Usefulness::Inconclusive)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn usefulness_wildcard<T, C, O>(
    oracle: &mut O,
    head_ty: &T,
    rest_types: &[T],
    matrix: &[Vec<Pattern<C>>],
    rest_query: &[Pattern<C>],
    budget: &mut Budget,
    depth: usize,
) -> Usefulness<C, O::Error>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    let seen = root_constructors(matrix);
    let space = match oracle.constructor_space(head_ty, &seen) {
        Ok(space) => space,
        Err(error) => return Usefulness::Inconclusive(InconclusiveReason::Oracle(error)),
    };

    match space {
        ConstructorSpace::Empty => Usefulness::Useless,
        ConstructorSpace::Complete { constructors } => {
            let constructors = deduplicate(constructors);
            if seen.iter().any(|head| !constructors.contains(head))
                || constructors.iter().any(|head| !seen.contains(head))
            {
                return Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle);
            }

            let mut first_inconclusive = None;
            for constructor in constructors {
                let field_types = match oracle.constructor_fields(head_ty, &constructor) {
                    Ok(ConstructorFields::Fields(fields)) => fields,
                    Ok(ConstructorFields::Impossible) => {
                        return Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle);
                    }
                    Err(error) => {
                        first_inconclusive.get_or_insert(InconclusiveReason::Oracle(error));
                        continue;
                    }
                };
                let specialized =
                    match specialize_matrix::<_, O::Error>(matrix, &constructor, field_types.len())
                    {
                        Ok(matrix) => matrix,
                        Err(reason) => {
                            first_inconclusive.get_or_insert(reason);
                            continue;
                        }
                    };
                let field_count = field_types.len();
                let mut next_types = field_types;
                next_types.extend_from_slice(rest_types);
                let mut next_query = vec![Pattern::Wildcard; field_count];
                next_query.extend_from_slice(rest_query);

                match recompose_constructor(
                    constructor,
                    field_count,
                    usefulness_rec(
                        oracle,
                        &next_types,
                        &specialized,
                        &next_query,
                        budget,
                        depth + 1,
                    ),
                ) {
                    useful @ Usefulness::Useful(_) => return useful,
                    Usefulness::Useless => {}
                    Usefulness::Inconclusive(reason) => {
                        first_inconclusive.get_or_insert(reason);
                    }
                }
            }

            first_inconclusive.map_or(Usefulness::Useless, Usefulness::Inconclusive)
        }
        ConstructorSpace::Incomplete { missing } => {
            let default = default_matrix(matrix);
            let rest_witness =
                match usefulness_rec(oracle, rest_types, &default, rest_query, budget, depth + 1) {
                    Usefulness::Useful(witness) => witness,
                    Usefulness::Useless => return Usefulness::Useless,
                    Usefulness::Inconclusive(reason) => {
                        return Usefulness::Inconclusive(reason);
                    }
                };

            if seen.is_empty() && matches!(&missing, MissingHead::Other) {
                return Usefulness::Useful(prepend(Witness::Wildcard, rest_witness));
            }

            let head_witness = match missing {
                MissingHead::Other => Witness::OtherThan { excluded: seen },
                MissingHead::Known(head) => {
                    if seen.contains(&head) {
                        return Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle);
                    }
                    let field_types = match oracle.constructor_fields(head_ty, &head) {
                        Ok(ConstructorFields::Fields(fields)) => fields,
                        Ok(ConstructorFields::Impossible) => {
                            return Usefulness::Inconclusive(
                                InconclusiveReason::InconsistentOracle,
                            );
                        }
                        Err(error) => {
                            return Usefulness::Inconclusive(InconclusiveReason::Oracle(error));
                        }
                    };
                    match inhabited(oracle, &field_types, &mut Vec::new(), budget, depth + 1) {
                        Ok(true) => {}
                        Ok(false) => {
                            return Usefulness::Inconclusive(
                                InconclusiveReason::InconsistentOracle,
                            );
                        }
                        Err(reason) => return Usefulness::Inconclusive(reason),
                    }
                    let field_witness = vec![Witness::Wildcard; field_types.len()];
                    if seen.is_empty() {
                        // No constructor row constrains this column. Retain the
                        // compact wildcard witness, but only after proving that
                        // the concrete missing head is actually inhabited.
                        Witness::Wildcard
                    } else {
                        Witness::Constructor {
                            head,
                            arguments: field_witness,
                        }
                    }
                }
            };
            Usefulness::Useful(prepend(head_witness, rest_witness))
        }
    }
}

/// Whether each of `types` has a value. The missing heads the oracle names
/// for a type are tried in turn until the fields of one have values.
/// `visiting` holds the types whose heads are being tried: a smallest value
/// of a type holds no other value of that type, so a head with a field of
/// such a type is passed over, as `Succ` of `Succ(Nat) | Zero` is for `Zero`.
fn inhabited<T, C, O>(
    oracle: &mut O,
    types: &[T],
    visiting: &mut Vec<T>,
    budget: &mut Budget,
    depth: usize,
) -> Result<bool, InconclusiveReason<O::Error>>
where
    T: Clone + Eq,
    C: Clone + Eq,
    O: ConstructorOracle<T, C>,
{
    for ty in types {
        if visiting.contains(ty) {
            return Ok(false);
        }
        visiting.push(ty.clone());
        let mut tried = Vec::new();
        let found = loop {
            budget.enter(depth)?;
            let head = match oracle
                .constructor_space(ty, &tried)
                .map_err(InconclusiveReason::Oracle)?
            {
                ConstructorSpace::Empty | ConstructorSpace::Complete { .. } => break false,
                ConstructorSpace::Incomplete {
                    missing: MissingHead::Other,
                } => break true,
                ConstructorSpace::Incomplete {
                    missing: MissingHead::Known(head),
                } => head,
            };
            let fields = match oracle
                .constructor_fields(ty, &head)
                .map_err(InconclusiveReason::Oracle)?
            {
                ConstructorFields::Fields(fields) if !tried.contains(&head) => fields,
                // A missing head is neither one already tried nor impossible.
                _ => return Err(InconclusiveReason::InconsistentOracle),
            };
            if inhabited(oracle, &fields, visiting, budget, depth + 1)? {
                break true;
            }
            tried.push(head);
        };
        visiting.pop();
        if !found {
            return Ok(false);
        }
    }
    Ok(true)
}

fn specialize_matrix<C, E>(
    matrix: &[Vec<Pattern<C>>],
    constructor: &C,
    field_count: usize,
) -> Result<Vec<Vec<Pattern<C>>>, InconclusiveReason<E>>
where
    C: Clone + Eq,
{
    let mut result = Vec::new();
    for row in matrix {
        let (head, rest) = row
            .split_first()
            .expect("specialization is only called for a non-empty matrix width");
        specialize_head(head, rest, constructor, field_count, &mut result)?;
    }
    Ok(result)
}

fn specialize_head<C, E>(
    pattern: &Pattern<C>,
    rest: &[Pattern<C>],
    constructor: &C,
    field_count: usize,
    output: &mut Vec<Vec<Pattern<C>>>,
) -> Result<(), InconclusiveReason<E>>
where
    C: Clone + Eq,
{
    let mut emit = |mut row: Vec<Pattern<C>>| {
        row.extend_from_slice(rest);
        output.push(row);
    };
    specialize_pattern(pattern, constructor, field_count, &mut emit).map_err(|mismatch| {
        InconclusiveReason::ArityMismatch {
            expected: mismatch.expected,
            actual: mismatch.actual,
        }
    })
}

fn default_matrix<C: Clone>(matrix: &[Vec<Pattern<C>>]) -> Vec<Vec<Pattern<C>>> {
    let mut result = Vec::new();
    for row in matrix {
        let (head, rest) = row
            .split_first()
            .expect("defaulting is only called for a non-empty matrix width");
        default_head(head, rest, &mut result);
    }
    result
}

fn default_head<C: Clone>(
    pattern: &Pattern<C>,
    rest: &[Pattern<C>],
    output: &mut Vec<Vec<Pattern<C>>>,
) {
    expand_default_pattern(pattern, &mut || output.push(rest.to_vec()));
}

fn root_constructors<C: Clone + Eq>(matrix: &[Vec<Pattern<C>>]) -> Vec<C> {
    let mut result = Vec::new();
    for row in matrix {
        if let Some(head) = row.first() {
            collect_root_constructors(head, &mut result);
        }
    }
    result
}

fn deduplicate<C: Eq>(constructors: Vec<C>) -> Vec<C> {
    constructors
        .into_iter()
        .fold(Vec::new(), |mut result, constructor| {
            if !result.contains(&constructor) {
                result.push(constructor);
            }
            result
        })
}

fn recompose_constructor<C, E>(
    head: C,
    field_count: usize,
    usefulness: Usefulness<C, E>,
) -> Usefulness<C, E> {
    match usefulness {
        Usefulness::Useful(mut witness) => {
            if witness.len() < field_count {
                return Usefulness::Inconclusive(InconclusiveReason::InconsistentOracle);
            }
            let rest = witness.split_off(field_count);
            let constructor = Witness::Constructor {
                head,
                arguments: witness,
            };
            Usefulness::Useful(prepend(constructor, rest))
        }
        Usefulness::Useless => Usefulness::Useless,
        Usefulness::Inconclusive(reason) => Usefulness::Inconclusive(reason),
    }
}

fn prepend<C>(head: Witness<C>, mut rest: Vec<Witness<C>>) -> Vec<Witness<C>> {
    rest.insert(0, head);
    rest
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ArityMismatch {
    pub(crate) expected: usize,
    pub(crate) actual: usize,
}

pub(crate) fn specialize_pattern<C, F>(
    pattern: &Pattern<C>,
    constructor: &C,
    field_count: usize,
    emit: &mut F,
) -> Result<(), ArityMismatch>
where
    C: Clone + Eq,
    F: FnMut(Vec<Pattern<C>>),
{
    match pattern {
        Pattern::Wildcard => emit(vec![Pattern::Wildcard; field_count]),
        Pattern::Constructor { head, arguments } if head == constructor => {
            if arguments.len() != field_count {
                return Err(ArityMismatch {
                    expected: field_count,
                    actual: arguments.len(),
                });
            }
            emit(arguments.clone());
        }
        Pattern::Constructor { .. } => {}
        Pattern::Or(alternatives) => {
            for alternative in alternatives {
                specialize_pattern(alternative, constructor, field_count, emit)?;
            }
        }
    }
    Ok(())
}

pub(crate) fn expand_default_pattern<C, F>(pattern: &Pattern<C>, emit: &mut F)
where
    F: FnMut(),
{
    match pattern {
        Pattern::Wildcard => emit(),
        Pattern::Constructor { .. } => {}
        Pattern::Or(alternatives) => {
            for alternative in alternatives {
                expand_default_pattern(alternative, emit);
            }
        }
    }
}

pub(crate) fn collect_root_constructors<C: Clone + Eq>(pattern: &Pattern<C>, output: &mut Vec<C>) {
    match pattern {
        Pattern::Wildcard => {}
        Pattern::Constructor { head, .. } => {
            if !output.contains(head) {
                output.push(head.clone());
            }
        }
        Pattern::Or(alternatives) => {
            for alternative in alternatives {
                collect_root_constructors(alternative, output);
            }
        }
    }
}

struct Budget {
    remaining: usize,
    config: Config,
}

impl Budget {
    fn new(config: Config) -> Self {
        Self {
            remaining: config.max_steps,
            config,
        }
    }

    fn enter<E>(&mut self, depth: usize) -> Result<(), InconclusiveReason<E>> {
        if depth > self.config.max_depth {
            return Err(InconclusiveReason::DepthLimitExceeded {
                max_depth: self.config.max_depth,
            });
        }
        let Some(remaining) = self.remaining.checked_sub(1) else {
            return Err(InconclusiveReason::StepLimitExceeded {
                max_steps: self.config.max_steps,
            });
        };
        self.remaining = remaining;
        Ok(())
    }
}
