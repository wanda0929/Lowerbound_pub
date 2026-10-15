use serde::{Deserialize, Serialize};

/// A sparse conic problem in the shared form
/// `minimize q'x` subject to `A*x + s = b`, `s in K`.
///
/// Clarabel consumes this form directly. The MOSEK adapter submits the
/// equivalent affine conic constraints `b - A*x in K`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ConicProblem {
    pub q: Vec<f64>,
    pub a: SparseMatrix,
    pub b: Vec<f64>,
    pub cones: Vec<Cone>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SparseMatrix {
    pub rows: usize,
    pub cols: usize,
    /// Sorted `(row, column, value)` entries with no duplicates or zeros.
    pub entries: Vec<(usize, usize, f64)>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Cone {
    Zero(usize),
    Nonnegative(usize),
    SecondOrder(usize),
    /// Lower-triangular svec dimension for an `side x side` PSD matrix.
    PsdTriangle(usize),
}

impl Cone {
    pub fn dimension(&self) -> usize {
        match *self {
            Self::Zero(dimension) | Self::Nonnegative(dimension) | Self::SecondOrder(dimension) => {
                dimension
            }
            Self::PsdTriangle(side) => side * (side + 1) / 2,
        }
    }
}

impl ConicProblem {
    pub fn validate(&self) -> Result<(), String> {
        if self.a.cols != self.q.len() {
            return Err("A column count must equal objective length".into());
        }
        if self.a.rows != self.b.len() {
            return Err("A row count must equal b length".into());
        }
        let cone_rows: usize = self.cones.iter().map(Cone::dimension).sum();
        if cone_rows != self.a.rows {
            return Err(format!(
                "cone dimensions total {cone_rows}, expected {} rows",
                self.a.rows
            ));
        }
        let mut previous = None;
        for &(row, column, value) in &self.a.entries {
            if row >= self.a.rows || column >= self.a.cols {
                return Err("sparse entry is out of bounds".into());
            }
            if !value.is_finite() || value == 0.0 {
                return Err("sparse values must be finite and nonzero".into());
            }
            let index = (column, row);
            if previous.is_some_and(|prior| prior >= index) {
                return Err("sparse entries must be unique and sorted by column then row".into());
            }
            previous = Some(index);
        }
        if self.q.iter().chain(&self.b).any(|value| !value.is_finite()) {
            return Err("q and b must be finite".into());
        }
        Ok(())
    }

    pub fn csc(&self) -> (Vec<usize>, Vec<usize>, Vec<f64>) {
        let mut column_pointers = vec![0; self.a.cols + 1];
        for &(_, column, _) in &self.a.entries {
            column_pointers[column + 1] += 1;
        }
        for column in 0..self.a.cols {
            column_pointers[column + 1] += column_pointers[column];
        }
        let rows = self.a.entries.iter().map(|entry| entry.0).collect();
        let values = self.a.entries.iter().map(|entry| entry.2).collect();
        (column_pointers, rows, values)
    }
}

/// Shared semidefinite adapter regression:
/// `minimize x` subject to `diag(1,x)` positive semidefinite.
pub fn adapter_regression_problem() -> ConicProblem {
    ConicProblem {
        q: vec![1.0],
        a: SparseMatrix {
            rows: 3,
            cols: 1,
            entries: vec![(2, 0, -1.0)],
        },
        b: vec![1.0, 0.0, 0.0],
        cones: vec![Cone::PsdTriangle(2)],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_and_converts_shared_problem() {
        let problem = adapter_regression_problem();
        assert_eq!(problem.validate(), Ok(()));
        assert_eq!(problem.csc(), (vec![0, 1], vec![2], vec![-1.0]));
    }

    #[test]
    fn rejects_cone_row_mismatch() {
        let mut problem = adapter_regression_problem();
        problem.cones = vec![Cone::Nonnegative(2)];
        assert!(problem.validate().unwrap_err().contains("cone dimensions"));
    }
}
