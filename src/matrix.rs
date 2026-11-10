use std::{convert::Infallible, error::Error, fmt};

use crate::{
    ConstructorFields, ConstructorOracle, ConstructorSpace, InputError, Pattern, Usefulness, engine,
};

/// One row in a [`PatternMatrix`].
///
/// The payload is opaque to `matchcov`. Operations that expand a row clone the
/// payload into every resulting row without inspecting it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternRow<C, R = ()> {
    patterns: Vec<Pattern<C>>,
    payload: R,
}

impl<C, R> PatternRow<C, R> {
    /// Creates a row from its patterns and caller-defined payload.
    pub fn new(patterns: impl IntoIterator<Item = Pattern<C>>, payload: R) -> Self {
        Self {
            patterns: patterns.into_iter().collect(),
            payload,
        }
    }

    /// Returns the patterns in column order.
    pub fn patterns(&self) -> &[Pattern<C>] {
        &self.patterns
    }

    /// Returns mutable access to the patterns without allowing the row width to
    /// change.
    pub fn patterns_mut(&mut self) -> &mut [Pattern<C>] {
        &mut self.patterns
    }

    /// Returns the caller-defined payload.
    pub fn payload(&self) -> &R {
        &self.payload
    }

    /// Returns mutable access to the caller-defined payload.
    pub fn payload_mut(&mut self) -> &mut R {
        &mut self.payload
    }

    /// Decomposes the row into its patterns and payload.
    pub fn into_parts(self) -> (Vec<Pattern<C>>, R) {
        (self.patterns, self.payload)
    }
}

/// A typed pattern matrix for reusable decision-tree operations.
///
/// Each column has one type, and every [`PatternRow`] always has exactly the
/// same number of patterns as there are column types. [`PatternMatrix::new`]
/// validates this invariant, and the mutation methods preserve it.
///
/// `Pattern<C>` describes only matching structure, while
/// [`ConstructorOracle`] supplies type-dependent constructor fields and spaces.
/// The matrix's payload type `R` remains entirely adapter-defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternMatrix<T, C, R = ()> {
    column_types: Vec<T>,
    rows: Vec<PatternRow<C, R>>,
}

impl<T, C, R> PatternMatrix<T, C, R> {
    /// Creates a matrix and validates that every row has one pattern per column.
    pub fn new(
        column_types: impl IntoIterator<Item = T>,
        rows: impl IntoIterator<Item = PatternRow<C, R>>,
    ) -> Result<Self, MatrixError<Infallible>> {
        let column_types: Vec<_> = column_types.into_iter().collect();
        let rows: Vec<_> = rows.into_iter().collect();

        for (row, entry) in rows.iter().enumerate() {
            if entry.patterns.len() != column_types.len() {
                return Err(MatrixError::RowWidth {
                    row,
                    expected: column_types.len(),
                    actual: entry.patterns.len(),
                });
            }
        }

        Ok(Self { column_types, rows })
    }

    /// Returns the column types in matrix order.
    pub fn column_types(&self) -> &[T] {
        &self.column_types
    }

    /// Returns the rows in deterministic input or expansion order.
    pub fn rows(&self) -> &[PatternRow<C, R>] {
        &self.rows
    }

    /// Returns the number of columns.
    pub fn width(&self) -> usize {
        self.column_types.len()
    }

    /// Returns the number of rows.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Returns whether the matrix contains no rows.
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Decomposes the matrix into its column types and rows.
    pub fn into_parts(self) -> (Vec<T>, Vec<PatternRow<C, R>>) {
        (self.column_types, self.rows)
    }

    /// Specializes an arbitrary column for `constructor`.
    ///
    /// The selected type and pattern are replaced in place by the constructor's
    /// field types and field patterns. Wildcards expand to field wildcards,
    /// matching constructors expand to their arguments, other constructors are
    /// discarded, and or-patterns expand recursively from left to right. When
    /// one alternative of a row specializes to patterns that match anything,
    /// the row specializes to one row of wildcards instead, which matches what
    /// all its alternatives do. Input row order is preserved, and every
    /// expanded row receives a clone of its original payload.
    ///
    /// An impossible constructor denotes an empty branch. In that case this
    /// returns a matrix with no rows and with the selected column removed; there
    /// are no constructor field columns to represent.
    pub fn specialize<O>(
        &self,
        oracle: &mut O,
        column: usize,
        constructor: &C,
    ) -> Result<Self, MatrixError<O::Error>>
    where
        T: Clone,
        C: Clone + Eq,
        R: Clone,
        O: ConstructorOracle<T, C>,
    {
        let column_type = self
            .column_types
            .get(column)
            .ok_or_else(|| self.column_error(column))?;
        let field_types = match oracle.constructor_fields(column_type, constructor) {
            Ok(ConstructorFields::Fields(fields)) => fields,
            Ok(ConstructorFields::Impossible) => {
                return Ok(Self {
                    column_types: remove_item(&self.column_types, column),
                    rows: Vec::new(),
                });
            }
            Err(error) => return Err(MatrixError::Oracle(error)),
        };

        let mut rows = Vec::new();
        for row in &self.rows {
            let replacements = engine::specialize_alternatives(
                &row.patterns[column],
                constructor,
                field_types.len(),
            )
            .map_err(|mismatch| MatrixError::ArityMismatch {
                expected: mismatch.expected,
                actual: mismatch.actual,
            })?;
            for replacement in replacements {
                let mut patterns =
                    Vec::with_capacity(row.patterns.len().saturating_sub(1) + replacement.len());
                patterns.extend_from_slice(&row.patterns[..column]);
                patterns.extend(replacement);
                patterns.extend_from_slice(&row.patterns[column + 1..]);
                rows.push(PatternRow::new(patterns, row.payload.clone()));
            }
        }

        Ok(Self {
            column_types: replace_item(&self.column_types, column, &field_types),
            rows,
        })
    }

    /// Removes an arbitrary column and keeps only its default-matching rows.
    ///
    /// Wildcards match the default case and constructors do not. A row whose
    /// or-pattern has a wildcard alternative, at any depth, is kept once. This
    /// differs from [`without_column`](Self::without_column), which retains
    /// every row without interpreting its selected pattern.
    pub fn specialize_default(&self, column: usize) -> Result<Self, MatrixError<Infallible>>
    where
        T: Clone,
        C: Clone,
        R: Clone,
    {
        self.check_column(column)?;

        let mut rows = Vec::new();
        for row in &self.rows {
            if engine::matches_anything(&row.patterns[column]) {
                rows.push(PatternRow::new(
                    remove_item(&row.patterns, column),
                    row.payload.clone(),
                ));
            }
        }

        Ok(Self {
            column_types: remove_item(&self.column_types, column),
            rows,
        })
    }

    /// Removes a column without filtering or expanding any row patterns.
    pub fn without_column(&self, column: usize) -> Result<Self, MatrixError<Infallible>>
    where
        T: Clone,
        C: Clone,
        R: Clone,
    {
        self.check_column(column)?;

        Ok(Self {
            column_types: remove_item(&self.column_types, column),
            rows: self
                .rows
                .iter()
                .map(|row| PatternRow::new(remove_item(&row.patterns, column), row.payload.clone()))
                .collect(),
        })
    }

    /// Swaps two columns in both the type vector and every row.
    ///
    /// Both indexes are checked before any mutation, so an error leaves the
    /// matrix unchanged.
    pub fn swap_columns(&mut self, lhs: usize, rhs: usize) -> Result<(), MatrixError<Infallible>> {
        self.check_column(lhs)?;
        self.check_column(rhs)?;

        self.column_types.swap(lhs, rhs);
        for row in &mut self.rows {
            row.patterns.swap(lhs, rhs);
        }
        Ok(())
    }

    /// Returns the observed constructor heads and constructor space for a column.
    ///
    /// `observed` is deduplicated in first-seen order: rows are visited in matrix
    /// order and nested or-patterns in depth-first, left-to-right order. Only
    /// root constructors of the selected pattern are observed. The oracle's
    /// [`ConstructorSpace`] value, including [`ConstructorSpace::Empty`], is
    /// returned unchanged.
    pub fn column_signature<O>(
        &self,
        oracle: &mut O,
        column: usize,
    ) -> Result<ColumnSignature<C>, MatrixError<O::Error>>
    where
        C: Clone + Eq,
        O: ConstructorOracle<T, C>,
    {
        let column_type = self
            .column_types
            .get(column)
            .ok_or_else(|| self.column_error(column))?;
        let mut observed = Vec::new();
        for row in &self.rows {
            engine::collect_root_constructors(&row.patterns[column], &mut observed);
        }
        let space = oracle
            .constructor_space(column_type, &observed)
            .map_err(MatrixError::Oracle)?;

        Ok(ColumnSignature { observed, space })
    }

    /// Tests one row against all of its predecessors using this matrix's column
    /// types.
    ///
    /// The row payload is ignored. Oracle failures, arity mismatches, and
    /// resource-limit failures retain the existing [`Usefulness::Inconclusive`]
    /// behavior; only an invalid row index is returned as a matrix error.
    pub fn row_usefulness<O>(
        &self,
        oracle: &mut O,
        row: usize,
    ) -> Result<Usefulness<C, O::Error>, MatrixError<O::Error>>
    where
        T: Clone + Eq,
        C: Clone + Eq,
        O: ConstructorOracle<T, C>,
    {
        let query = self.rows.get(row).ok_or(MatrixError::RowOutOfBounds {
            row,
            rows: self.rows.len(),
        })?;
        let predecessors: Vec<_> = self.rows[..row]
            .iter()
            .map(|entry| entry.patterns.clone())
            .collect();

        engine::usefulness(oracle, &self.column_types, &predecessors, &query.patterns).map_err(
            |error| match error {
                InputError::MatrixRowWidth {
                    row,
                    expected,
                    actual,
                } => MatrixError::RowWidth {
                    row,
                    expected,
                    actual,
                },
                InputError::QueryWidth { expected, actual } => MatrixError::RowWidth {
                    row,
                    expected,
                    actual,
                },
            },
        )
    }

    fn check_column(&self, column: usize) -> Result<(), MatrixError<Infallible>> {
        if column < self.column_types.len() {
            Ok(())
        } else {
            Err(self.column_error(column))
        }
    }

    fn column_error<E>(&self, column: usize) -> MatrixError<E> {
        MatrixError::ColumnOutOfBounds {
            column,
            columns: self.column_types.len(),
        }
    }
}

/// Constructor information for one matrix column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnSignature<C> {
    /// Constructor roots observed in deterministic first-seen order.
    pub observed: Vec<C>,
    /// The constructor space reported by the oracle for the selected column.
    pub space: ConstructorSpace<C>,
}

/// An invalid pattern-matrix operation or failed oracle query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatrixError<E = Infallible> {
    /// A row has a different width than the column type vector.
    RowWidth {
        /// Zero-based row index.
        row: usize,
        /// Number of column types.
        expected: usize,
        /// Number of patterns in the row.
        actual: usize,
    },
    /// A column index is outside the matrix width.
    ColumnOutOfBounds {
        /// Requested zero-based column index.
        column: usize,
        /// Number of columns in the matrix.
        columns: usize,
    },
    /// A row index is outside the matrix length.
    RowOutOfBounds {
        /// Requested zero-based row index.
        row: usize,
        /// Number of rows in the matrix.
        rows: usize,
    },
    /// The constructor oracle could not supply a requested fact.
    Oracle(E),
    /// A matching constructor pattern has a different arity than its type.
    ArityMismatch {
        /// Arity reported by the oracle.
        expected: usize,
        /// Arity present in the pattern.
        actual: usize,
    },
}

impl<E: fmt::Display> fmt::Display for MatrixError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RowWidth {
                row,
                expected,
                actual,
            } => write!(
                f,
                "pattern matrix row {row} has width {actual}, expected {expected}"
            ),
            Self::ColumnOutOfBounds { column, columns } => write!(
                f,
                "pattern matrix column {column} is out of bounds for width {columns}"
            ),
            Self::RowOutOfBounds { row, rows } => {
                write!(
                    f,
                    "pattern matrix row {row} is out of bounds for {rows} rows"
                )
            }
            Self::Oracle(error) => write!(f, "constructor oracle failed: {error}"),
            Self::ArityMismatch { expected, actual } => write!(
                f,
                "constructor pattern has arity {actual}, expected {expected}"
            ),
        }
    }
}

impl<E> Error for MatrixError<E>
where
    E: Error + 'static,
{
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Oracle(error) => Some(error),
            _ => None,
        }
    }
}

fn remove_item<T: Clone>(items: &[T], index: usize) -> Vec<T> {
    let mut result = Vec::with_capacity(items.len().saturating_sub(1));
    result.extend_from_slice(&items[..index]);
    result.extend_from_slice(&items[index + 1..]);
    result
}

fn replace_item<T: Clone>(items: &[T], index: usize, replacement: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(items.len().saturating_sub(1) + replacement.len());
    result.extend_from_slice(&items[..index]);
    result.extend_from_slice(replacement);
    result.extend_from_slice(&items[index + 1..]);
    result
}
