import Mathlib
import NDEAMathlibGate.CayleyInverseCompassV1R3
import NDEAMathlibGate.CayleyStrongerMatrixComplexV6R

open Matrix

namespace NDEAMathlibGate
namespace CayleyInverseNativeComplexLiftV1R2

/-!
Native Mathlib Complex Cayley inverse lift V1R2.

Repair over V1R:
  The V1R source reached the inverse and unitarity theorem names but failed
  at U_formula because Lean normalized (-I)*x into -(I*x).
  This V1R2 module adds scalar lemmas matching those exact normalized forms.

Scope:
  finite 2x2 concrete example only;
  not a general Cayley theorem;
  not an operator/PML theorem;
  not a continuous PDE theorem.
-/

abbrev MatrixState := Matrix (Fin 2) (Fin 2) Complex

def matmul2 (A B : MatrixState) : MatrixState :=
  !![ A 0 0 * B 0 0 + A 0 1 * B 1 0,
      A 0 0 * B 0 1 + A 0 1 * B 1 1;
      A 1 0 * B 0 0 + A 1 1 * B 1 0,
      A 1 0 * B 0 1 + A 1 1 * B 1 1 ]

def trace2 (A : MatrixState) : Complex :=
  A 0 0 + A 1 1

def det2 (A : MatrixState) : Complex :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

def id_matrix : MatrixState :=
  !![1, 0; 0, 1]

def zero_matrix : MatrixState :=
  !![0, 0; 0, 0]

def hC : Complex :=
  (((1 : Rat) / 2 : Rat) : Complex)

def negIhalf : Complex :=
  -(hC * Complex.I)

/-- L = I + iH for H = [[0,1],[1,0]] and alpha = 1. -/
def L : MatrixState :=
  !![1, Complex.I; Complex.I, 1]

/-- R = I - iH for H = [[0,1],[1,0]] and alpha = 1. -/
def R : MatrixState :=
  !![1, -Complex.I; -Complex.I, 1]

/-- Correct inverse of L. -/
def L_inv : MatrixState :=
  !![hC, negIhalf; negIhalf, hC]

theorem scalar_diag_left :
    hC + negIhalf * Complex.I = 1 := by
  dsimp [hC, negIhalf]
  calc
    (((1 : Rat) / 2 : Rat) : Complex) +
      (-((((1 : Rat) / 2 : Rat) : Complex) * Complex.I)) * Complex.I
        =
      (((1 : Rat) / 2 : Rat) : Complex) -
        ((((1 : Rat) / 2 : Rat) : Complex) * (Complex.I * Complex.I)) := by
            ring
    _ =
      (((1 : Rat) / 2 : Rat) : Complex) -
        ((((1 : Rat) / 2 : Rat) : Complex) * (-1)) := by
            rw [Complex.I_mul_I]
    _ = 1 := by
            norm_num

theorem scalar_diag_left_comm :
    negIhalf * Complex.I + hC = 1 := by
  rw [add_comm]
  exact scalar_diag_left

theorem scalar_diag_right :
    hC + Complex.I * negIhalf = 1 := by
  dsimp [hC, negIhalf]
  calc
    (((1 : Rat) / 2 : Rat) : Complex) +
      Complex.I * (-((((1 : Rat) / 2 : Rat) : Complex) * Complex.I))
        =
      (((1 : Rat) / 2 : Rat) : Complex) -
        ((((1 : Rat) / 2 : Rat) : Complex) * (Complex.I * Complex.I)) := by
            ring
    _ =
      (((1 : Rat) / 2 : Rat) : Complex) -
        ((((1 : Rat) / 2 : Rat) : Complex) * (-1)) := by
            rw [Complex.I_mul_I]
    _ = 1 := by
            norm_num

theorem scalar_diag_right_comm :
    Complex.I * negIhalf + hC = 1 := by
  rw [add_comm]
  exact scalar_diag_right

theorem scalar_offdiag_a :
    hC * Complex.I + negIhalf = 0 := by
  dsimp [hC, negIhalf]
  ring

theorem scalar_offdiag_b :
    negIhalf + hC * Complex.I = 0 := by
  rw [add_comm]
  exact scalar_offdiag_a

theorem scalar_offdiag_c :
    negIhalf + Complex.I * hC = 0 := by
  dsimp [hC, negIhalf]
  ring

theorem scalar_offdiag_d :
    Complex.I * hC + negIhalf = 0 := by
  rw [add_comm]
  exact scalar_offdiag_c

theorem L_left_inverse :
    matmul2 L_inv L = id_matrix := by
  change (fun i j => (matmul2 L_inv L) i j) = (fun i j => id_matrix i j)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matmul2, L_inv, L, id_matrix,
      scalar_diag_left, scalar_diag_left_comm,
      scalar_offdiag_a, scalar_offdiag_b]

theorem L_right_inverse :
    matmul2 L L_inv = id_matrix := by
  change (fun i j => (matmul2 L L_inv) i j) = (fun i j => id_matrix i j)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matmul2, L_inv, L, id_matrix,
      scalar_diag_right, scalar_diag_right_comm,
      scalar_offdiag_c, scalar_offdiag_d]

theorem det2_L :
    det2 L = 2 := by
  dsimp [det2, L]
  rw [Complex.I_mul_I]
  norm_num

theorem det2_L_nonzero :
    det2 L ≠ 0 := by
  rw [det2_L]
  norm_num

/-- Finite Cayley transform U = R * L_inv. -/
def U : MatrixState :=
  matmul2 R L_inv

def U_expected : MatrixState :=
  !![0, -Complex.I; -Complex.I, 0]

/- These are the exact normalized forms Lean produced in the failed V1R U_formula. -/
theorem scalar_U_diag_a :
    hC + -(Complex.I * negIhalf) = 0 := by
  dsimp [hC, negIhalf]
  calc
    (((1 : Rat) / 2 : Rat) : Complex) +
      -(Complex.I * (-((((1 : Rat) / 2 : Rat) : Complex) * Complex.I)))
        =
      (((1 : Rat) / 2 : Rat) : Complex) +
        ((((1 : Rat) / 2 : Rat) : Complex) * (Complex.I * Complex.I)) := by
            ring
    _ =
      (((1 : Rat) / 2 : Rat) : Complex) +
        ((((1 : Rat) / 2 : Rat) : Complex) * (-1)) := by
            rw [Complex.I_mul_I]
    _ = 0 := by
            norm_num

theorem scalar_U_diag_b :
    -(Complex.I * negIhalf) + hC = 0 := by
  rw [add_comm]
  exact scalar_U_diag_a

theorem scalar_U_offdiag_a :
    negIhalf + -(Complex.I * hC) = -Complex.I := by
  dsimp [hC, negIhalf]
  ring

theorem scalar_U_offdiag_b :
    -(Complex.I * hC) + negIhalf = -Complex.I := by
  rw [add_comm]
  exact scalar_U_offdiag_a

theorem U_formula :
    U = U_expected := by
  change (fun i j => U i j) = (fun i j => U_expected i j)
  funext i j
  fin_cases i <;> fin_cases j
  · simpa [U, matmul2, R, L_inv, U_expected] using scalar_U_diag_a
  · simpa [U, matmul2, R, L_inv, U_expected] using scalar_U_offdiag_a
  · simpa [U, matmul2, R, L_inv, U_expected] using scalar_U_offdiag_b
  · simpa [U, matmul2, R, L_inv, U_expected] using scalar_U_diag_b

def U_adj : MatrixState :=
  !![0, Complex.I; Complex.I, 0]

theorem scalar_I_negI :
    Complex.I * (-Complex.I) = 1 := by
  calc
    Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by
      ring
    _ = -(-1 : Complex) := by
      rw [Complex.I_mul_I]
    _ = 1 := by
      norm_num

theorem scalar_negI_I :
    (-Complex.I) * Complex.I = 1 := by
  rw [mul_comm]
  exact scalar_I_negI

theorem U_expected_unitary_left :
    matmul2 U_adj U_expected = id_matrix := by
  change (fun i j => (matmul2 U_adj U_expected) i j) = (fun i j => id_matrix i j)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matmul2, U_adj, U_expected, id_matrix, scalar_I_negI, scalar_negI_I]

theorem U_expected_unitary_right :
    matmul2 U_expected U_adj = id_matrix := by
  change (fun i j => (matmul2 U_expected U_adj) i j) = (fun i j => id_matrix i j)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matmul2, U_adj, U_expected, id_matrix, scalar_I_negI, scalar_negI_I]

theorem U_unitary_left :
    matmul2 U_adj U = id_matrix := by
  rw [U_formula]
  exact U_expected_unitary_left

theorem U_unitary_right :
    matmul2 U U_adj = id_matrix := by
  rw [U_formula]
  exact U_expected_unitary_right

/-- V6R stress-boundary matrix; singular and separate from invertible L. -/
def V6R_stress_boundary : MatrixState :=
  !![1, Complex.I; -Complex.I, 1]

theorem det2_V6R_stress_boundary_zero :
    det2 V6R_stress_boundary = 0 := by
  dsimp [det2, V6R_stress_boundary]
  rw [scalar_I_negI]
  norm_num

theorem fake_inverse_does_not_invert_V6R_stress_boundary :
    matmul2 id_matrix V6R_stress_boundary ≠ id_matrix := by
  intro h0
  have h01 := congrArg (fun M : MatrixState => M 0 1) h0
  have hI0 : Complex.I = 0 := by
    simpa [matmul2, id_matrix, V6R_stress_boundary] using h01
  have hbad : (-1 : Complex) = 0 := by
    calc
      (-1 : Complex) = Complex.I * Complex.I := by
        simpa using (Eq.symm Complex.I_mul_I)
      _ = 0 := by
        rw [hI0]
        ring
  norm_num at hbad

theorem fallback_exact_pair_left_inverse :
    NDEAMathlibGate.CayleyInverseCompassV1R3.matmul2
      NDEAMathlibGate.CayleyInverseCompassV1R3.L_inv
      NDEAMathlibGate.CayleyInverseCompassV1R3.L =
    NDEAMathlibGate.CayleyInverseCompassV1R3.id_matrix := by
  exact NDEAMathlibGate.CayleyInverseCompassV1R3.L_left_inverse

theorem fallback_exact_pair_unitary_left :
    NDEAMathlibGate.CayleyInverseCompassV1R3.matmul2
      NDEAMathlibGate.CayleyInverseCompassV1R3.U_adj
      NDEAMathlibGate.CayleyInverseCompassV1R3.U =
    NDEAMathlibGate.CayleyInverseCompassV1R3.id_matrix := by
  exact NDEAMathlibGate.CayleyInverseCompassV1R3.U_unitary_left

def nativeComplexLiftStatusV1R2 : String :=
  "native_complex_lift_validated"

def fallbackReferenceV1R2 : String :=
  "CayleyInverseCompassV1R3_exact_pair_model_verified"

def continuousPDEFormalizationStatusNativeComplexLiftV1R2 : String :=
  "not_claimed"

theorem true_native_complex_lift_status :
    nativeComplexLiftStatusV1R2 = "native_complex_lift_validated" := by
  rfl

theorem true_fallback_reference :
    fallbackReferenceV1R2 = "CayleyInverseCompassV1R3_exact_pair_model_verified" := by
  rfl

theorem true_continuousPDE_status_not_claimed :
    continuousPDEFormalizationStatusNativeComplexLiftV1R2 = "not_claimed" := by
  rfl

#check L_left_inverse
#check L_right_inverse
#check det2_L_nonzero
#check U_formula
#check U_unitary_left
#check U_unitary_right
#check det2_V6R_stress_boundary_zero
#check fake_inverse_does_not_invert_V6R_stress_boundary
#check fallback_exact_pair_left_inverse

end CayleyInverseNativeComplexLiftV1R2
end NDEAMathlibGate
