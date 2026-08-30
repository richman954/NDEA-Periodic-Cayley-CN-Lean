import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic

open Matrix
open Complex

-- True Control
theorem control_true : (1 : ℂ) + 1 = 2 := by ring

-- Stronger Matrix Complex Determinant Candidate
def hermitian_test_matrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, I; -I, 1]

theorem det_hermitian_test_matrix : hermitian_test_matrix.det = 0 := by
  rw [hermitian_test_matrix, Matrix.det_fin_two]
  -- Force Lean to evaluate the matrix indexing to raw scalars
  change 1 * 1 - I * (-I) = 0
  -- Map to I^2 and eliminate using the mathlib identity
  calc
    1 * 1 - I * (-I) = 1 + I ^ 2 := by ring
    _ = 1 + -1 := by rw [Complex.I_sq]
    _ = 0 := by ring
