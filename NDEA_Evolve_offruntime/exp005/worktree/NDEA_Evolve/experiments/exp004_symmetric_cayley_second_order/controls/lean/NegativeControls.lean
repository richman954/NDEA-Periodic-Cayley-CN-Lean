import NDEAEvolve.Experiments.Exp004.SymmetricCayleyGlobal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Experiment 004 focused mathematical controls

Endpoint controls instantiate the actual operator scheme. Exact scalar
witnesses detect changes to its three-factor composition and parameter scale;
their coefficients are connected to the production continuous linear map.
The Pauli witness separately detects the quadratic commutator term that a
nonsymmetric composition leaves behind. Scalar witnesses alone would not
demonstrate that noncommutative quadratic defect.

Scalar Cayley calculations and Pauli definitions follow the corresponding
Experiment 002 and Experiment 003 controls, repeated in a separate namespace
without changing or importing the predecessor controls files.
-/

noncomputable section

open Filter Matrix
open scoped Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004.Controls

/-- Every finite count is exact at zero physical time, including N=0. -/
theorem zero_time_exact {n : ℕ} (A B : Mat n) (N : ℕ) :
    symmetricStepHat A B ((0 : ℝ) / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) := by
  have hz : ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp
  rw [hz, NormedSpace.exp_zero]
  simp [symmetricStepHat, Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

/-- Zero powers agree independently of the positive-count fixed-time theorem. -/
theorem zero_power_identity {n : ℕ} (A B : Mat n) (h : ℝ) :
    symmetricStepHat A B h ^ 0 = (1 : E n →L[ℂ] E n) ∧
      exactStepHat (A + B) (h / 2) ^ 0 = (1 : E n →L[ℂ] E n) := by
  simp

/-- Zero generators remain exact for arbitrary real time and count. -/
theorem zero_generators_exact (n : ℕ) (t : ℝ) (N : ℕ) :
    symmetricStepHat (0 : Mat n) 0 (t / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) := by
  have hz : ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp [operatorOf]
  rw [hz, NormedSpace.exp_zero]
  simp [symmetricStepHat, Chat, operatorOf, cayley, cayleyN, cayleyR, cayleyD,
    skewPart, cscalar]

/-- The theorem retains dimension zero without assuming norm(identity)=1. -/
theorem zero_dimension_exact (A B : Mat 0) (t : ℝ) (N : ℕ) :
    symmetricStepHat A B (t / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)) := by
  exact Subsingleton.elim _ _

/-- Negative physical time satisfies the same nonnegative cubic majorant. -/
theorem negative_time_bound {n : ℕ} (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ (N : ℝ)) :
    ‖symmetricStepHat A B ((-1 : ℝ) / (N : ℝ)) ^ N -
        NormedSpace.exp
          ((-Complex.I * ((-1 : ℝ) : ℂ)) • operatorOf (A + B))‖ ≤
      1000 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2 := by
  simpa using symmetric_cayley_fixed_time_error_le (-1) A B N hA hB hN
    (by simpa using hstep)

def scalarCayley (alpha : ℝ) : ℂ :=
  (1 - Complex.I * (alpha : ℂ)) / (1 + Complex.I * (alpha : ℂ))

private theorem scalar_denominator_ne_zero (alpha : ℝ) :
    (1 + Complex.I * (alpha : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem scalarCayley_matrix_entry (alpha : ℝ) :
    cayley alpha (1 : Mat 1) 0 0 = scalarCayley alpha := by
  simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar,
    Matrix.mul_apply, Matrix.inv_subsingleton, Ring.inverse_eq_inv,
    scalarCayley, div_eq_mul_inv]

theorem scalarCayley_one : scalarCayley 1 = -Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero 1)).2
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

theorem scalarCayley_half :
    scalarCayley (1 / 2) = ((3 : ℂ) - 4 * Complex.I) / 5 := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero (1 / 2))).2
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

def scalarSymmetric (h : ℝ) : ℂ :=
  scalarCayley (h / 4) * scalarCayley (h / 2) * scalarCayley (h / 4)

def scalarNonsymmetric (h : ℝ) : ℂ :=
  scalarCayley (h / 2) * scalarCayley (h / 2)

def scalarWrongQuarterStep (h : ℝ) : ℂ :=
  scalarCayley (h / 2) * scalarCayley (h / 2) * scalarCayley (h / 2)

def scalarSymmetricMatrix (h : ℝ) : Mat 1 :=
  cayley (h / 4) 1 * cayley (h / 2) 1 * cayley (h / 4) 1

theorem scalarSymmetric_matrix_entry (h : ℝ) :
    scalarSymmetricMatrix h 0 0 = scalarSymmetric h := by
  simp [scalarSymmetricMatrix, scalarSymmetric, Matrix.mul_apply,
    scalarCayley_matrix_entry]

/-- The production operator is the image of the stated ordered matrix
composition, including the mixed zero/unit generator example below. -/
theorem symmetricStepHat_matrix_bridge {n : ℕ} (A B : Mat n) (h : ℝ) :
    symmetricStepHat A B h =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
        (cayley (h / 4) A * cayley (h / 2) B * cayley (h / 4) A) := by
  simp only [symmetricStepHat, Chat, map_mul]

/-- The exact scalar coefficient multiplies identity in the production
symmetric continuous-linear-map representation. -/
theorem scalarSymmetric_operator_bridge (h : ℝ) :
    symmetricStepHat (1 : Mat 1) 1 h =
      scalarSymmetric h • (1 : E 1 →L[ℂ] E 1) := by
  have hm : scalarSymmetricMatrix h = scalarSymmetric h • (1 : Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using scalarSymmetric_matrix_entry h
  calc
    symmetricStepHat (1 : Mat 1) 1 h =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1) (scalarSymmetricMatrix h) := by
      simp only [symmetricStepHat, Chat, scalarSymmetricMatrix, map_mul]
    _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
        (scalarSymmetric h • (1 : Mat 1)) := by rw [hm]
    _ = scalarSymmetric h • (1 : E 1 →L[ℂ] E 1) := by simp

theorem scalarSymmetric_two_re : (scalarSymmetric 2).re = -24 / 25 := by
  have hquarter : (2 : ℝ) / 4 = 1 / 2 := by norm_num
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarSymmetric, hquarter, hhalf, scalarCayley_half, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem scalarNonsymmetric_two_re : (scalarNonsymmetric 2).re = -1 := by
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarNonsymmetric, hhalf, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem scalarWrongQuarterStep_two_re : (scalarWrongQuarterStep 2).re = 0 := by
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarWrongQuarterStep, hhalf, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- The symmetric composition is a different finite scheme even for
commuting scalar generators. This does not assert a rate obstruction. -/
theorem symmetric_vs_nonsymmetric_detected :
    scalarSymmetric 2 ≠ scalarNonsymmetric 2 := by
  intro h
  have hre := congrArg Complex.re h
  rw [scalarSymmetric_two_re, scalarNonsymmetric_two_re] at hre
  norm_num at hre

/-- Replacing the outer quarter-step parameters by half-step parameters
changes the exact scalar coefficient. -/
theorem wrong_quarterstep_detected :
    scalarSymmetric 2 ≠ scalarWrongQuarterStep 2 := by
  intro h
  have hre := congrArg Complex.re h
  rw [scalarSymmetric_two_re, scalarWrongQuarterStep_two_re] at hre
  norm_num at hre

private theorem scalarCayley_ne_neg_one (alpha : ℝ) : scalarCayley alpha ≠ -1 := by
  intro h
  have heq := (div_eq_iff (scalar_denominator_ne_zero alpha)).mp h
  have hre := congrArg Complex.re heq
  norm_num at hre

/-- At A=0, B=I, physical time π, and N=1, the symmetric matrix step has
the scalar entry C(π/2), which differs from the exact scalar exponential -1.
The preceding matrix bridge ties this product to `symmetricStepHat`.
This rejects finite equality; no small-step error-bound violation is asserted. -/
theorem finite_step_exponential_equality_rejected :
    (cayley (Real.pi / 4) (0 : Mat 1) * cayley (Real.pi / 2) 1 *
        cayley (Real.pi / 4) 0 : Mat 1) 0 0 ≠
      Complex.exp (-Complex.I * (Real.pi : ℂ)) := by
  have hzero : cayley (Real.pi / 4) (0 : Mat 1) = 1 := by
    simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]
  rw [hzero, one_mul, mul_one, scalarCayley_matrix_entry]
  have hexp : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    convert Complex.exp_neg_pi_mul_I using 1 <;> ring
  rw [hexp]
  exact scalarCayley_ne_neg_one (Real.pi / 2)

def pauliX : Mat 2 := !![0, 1; 1, 0]

def pauliZ : Mat 2 := !![1, 0; 0, -1]

theorem pauliX_hermitian : pauliX.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose_apply]

theorem pauli_noncommutation : ¬ Commute pauliX pauliZ := by
  intro h
  have h01 := congrFun (congrFun h.eq (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- After multiplying physical-time quadratic Taylor coefficients by minus
two, an ordered A B product has A²+B²+2AB; the exponential has (A+B)². The off-diagonal
entry of this Hermitian Pauli example proves these coefficients differ. -/
theorem nonsymmetric_quadratic_mismatch :
    pauliX ^ 2 + pauliZ ^ 2 + pauliX * pauliZ + pauliX * pauliZ ≠
      (pauliX + pauliZ) ^ 2 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.add_apply] at h01

end NDEAEvolve.Exp004.Controls

#print axioms NDEAEvolve.Exp004.Controls.zero_time_exact
#print axioms NDEAEvolve.Exp004.Controls.zero_power_identity
#print axioms NDEAEvolve.Exp004.Controls.zero_generators_exact
#print axioms NDEAEvolve.Exp004.Controls.zero_dimension_exact
#print axioms NDEAEvolve.Exp004.Controls.negative_time_bound
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_matrix_entry
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_one
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_half
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_matrix_entry
#print axioms NDEAEvolve.Exp004.Controls.symmetricStepHat_matrix_bridge
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_operator_bridge
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_two_re
#print axioms NDEAEvolve.Exp004.Controls.scalarNonsymmetric_two_re
#print axioms NDEAEvolve.Exp004.Controls.scalarWrongQuarterStep_two_re
#print axioms NDEAEvolve.Exp004.Controls.symmetric_vs_nonsymmetric_detected
#print axioms NDEAEvolve.Exp004.Controls.wrong_quarterstep_detected
#print axioms NDEAEvolve.Exp004.Controls.finite_step_exponential_equality_rejected
#print axioms NDEAEvolve.Exp004.Controls.pauliX_hermitian
#print axioms NDEAEvolve.Exp004.Controls.pauliZ_hermitian
#print axioms NDEAEvolve.Exp004.Controls.pauli_noncommutation
#print axioms NDEAEvolve.Exp004.Controls.nonsymmetric_quadratic_mismatch
