import NDEAEvolve.Experiments.Exp003.ContinuousExponentialLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum

/-!
# Experiment 003 Step 5 focused controls

The endpoint controls instantiate the operator statements at zero time,
negative time, zero dimension, and zero powers. The scalar controls use the
same Cayley convention and are linked to the sole matrix entry in dimension
one. They detect sign and half-step changes by exact arithmetic.

The finite-step counterexample compares the scalar Cayley step at time π
with the scalar continuous exponential. It does not assert that the local
small-step hypothesis holds at that time, nor does it assert a failure of
the asymptotic convergence theorem.

The proof pattern for `scalarCayley_one` follows the existing Experiment 002
`AdversarialWitnesses.scalarCayley_one` control; it is repeated here so that
this Step-5 evidence does not import unrelated adversarial controls.
-/

noncomputable section

open Filter
open scoped Topology
open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003.Step5Controls

/-- At time zero every finite step count gives the exact identity, including
the separate `N = 0` endpoint. -/
theorem zero_time_exact {n : ℕ} (A B : Mat n) (N : ℕ) :
    splitStepHat A B ((0 : ℝ) / (2 * (N : ℝ))) ^ N =
      NormedSpace.exp ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) := by
  have hz : ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp
  rw [hz, NormedSpace.exp_zero]
  simp [splitStepHat, Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

/-- Zero powers always agree with each other. This statement does not
identify a zero-power approximation with evolution at an arbitrary time. -/
theorem zero_power_identity {n : ℕ} (A B : Mat n) (alpha : ℝ) :
    splitStepHat A B alpha ^ 0 = (1 : E n →L[ℂ] E n) ∧
      exactStepHat (A + B) alpha ^ 0 = (1 : E n →L[ℂ] E n) := by
  simp

/-- Zero generators give the identity at every physical time and step count. -/
theorem zero_generators_exact (n : ℕ) (t : ℝ) (N : ℕ) :
    splitStepHat (0 : Mat n) 0 (t / (2 * (N : ℝ))) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) := by
  have hz : ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp [operatorOf]
  rw [hz, NormedSpace.exp_zero]
  simp [splitStepHat, Chat, operatorOf, cayley, cayleyN, cayleyR, cayleyD,
    skewPart, cscalar]

/-- In zero dimension there is only one continuous endomorphism. -/
theorem zero_dimension_exact (A B : Mat 0) (t : ℝ) (N : ℕ) :
    splitStepHat A B (t / (2 * (N : ℝ))) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)) := by
  exact Subsingleton.elim _ _

/-- The operator convergence theorem accepts negative physical time. -/
theorem negative_time_convergence {n : ℕ} (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun N : ℕ => splitStepHat A B ((-1 : ℝ) / (2 * (N : ℝ))) ^ N)
      atTop
      (𝓝 (NormedSpace.exp
        ((-Complex.I * ((-1 : ℝ) : ℂ)) • operatorOf (A + B)))) :=
  split_cayley_fixed_time_tendsto_exp (-1) A B hA hB

/-- The quantitative bound also accepts negative time; the cubic numerator
is positive because it uses the absolute value of time. -/
theorem negative_time_bound {n : ℕ} (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * ‖operatorOf (A + B)‖ ≤ (N : ℝ)) :
    ‖splitStepHat A B ((-1 : ℝ) / (2 * (N : ℝ))) ^ N -
        NormedSpace.exp
          ((-Complex.I * ((-1 : ℝ) : ℂ)) • operatorOf (A + B))‖ ≤
      1 / (N : ℝ) * ‖operatorOf A‖ * ‖operatorOf B‖ +
        (9 / 4 : ℝ) * ‖operatorOf (A + B)‖ ^ 3 / (N : ℝ) ^ 2 := by
  simpa using split_cayley_fixed_time_error_le (-1) A B N hA hB hN
    (by simpa using hstep)

/-- Scalar Cayley transform of the unit Hermitian generator. -/
def scalarCayley (alpha : ℝ) : ℂ :=
  (1 - Complex.I * (alpha : ℂ)) / (1 + Complex.I * (alpha : ℂ))

/-- The scalar witnesses are the actual entry of the one-dimensional
matrix Cayley transform used by the production modules. -/
theorem scalarCayley_matrix_entry (alpha : ℝ) :
    cayley alpha (1 : Mat 1) 0 0 = scalarCayley alpha := by
  simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar,
    Matrix.mul_apply, Matrix.inv_subsingleton, Ring.inverse_eq_inv,
    scalarCayley, div_eq_mul_inv]

private theorem scalar_denominator_ne_zero (alpha : ℝ) :
    (1 + Complex.I * (alpha : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem scalarCayley_zero : scalarCayley 0 = 1 := by
  simp [scalarCayley]

theorem scalarCayley_one : scalarCayley 1 = -Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero 1)).2
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

theorem scalarCayley_neg_one : scalarCayley (-1) = Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero (-1))).2
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

/-- Reversing the sign of the Cayley parameter changes the exact result. -/
theorem sign_reversal_detected : scalarCayley (-1) ≠ scalarCayley 1 := by
  rw [scalarCayley_neg_one, scalarCayley_one]
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- Omitting the factor two in the physical-time parameter changes the
one-step approximation already for scalar unit generators. -/
theorem missing_halfstep_detected : scalarCayley (1 / 2) ≠ scalarCayley 1 := by
  rw [scalarCayley_half, scalarCayley_one]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- Refining one step into two half steps is not an exact Cayley semigroup
identity. Convergence does not assert equality of finite refinements. -/
theorem finite_refinement_equality_rejected :
    scalarCayley (1 / 2) ^ 2 ≠ scalarCayley 1 := by
  rw [scalarCayley_half, scalarCayley_one]
  intro h
  have hre := congrArg Complex.re h
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre

/-- A finite real scalar Cayley parameter never reaches the value -1. -/
theorem scalarCayley_ne_neg_one (alpha : ℝ) : scalarCayley alpha ≠ -1 := by
  intro h
  have heq := (div_eq_iff (scalar_denominator_ne_zero alpha)).mp h
  have hre := congrArg Complex.re heq
  norm_num at hre

/-- At physical time π the exact scalar exponential equals -1, whereas
the one-step Cayley approximation with α = π/2 does not. -/
theorem finite_step_exponential_equality_rejected :
    cayley (Real.pi / 2) (1 : Mat 1) 0 0 ≠
      Complex.exp (-Complex.I * (Real.pi : ℂ)) := by
  rw [scalarCayley_matrix_entry]
  have hexp : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    convert Complex.exp_neg_pi_mul_I using 1 <;> ring
  rw [hexp]
  exact scalarCayley_ne_neg_one (Real.pi / 2)

end NDEAEvolve.Exp003.Step5Controls

#print axioms NDEAEvolve.Exp003.Step5Controls.zero_time_exact
#print axioms NDEAEvolve.Exp003.Step5Controls.zero_power_identity
#print axioms NDEAEvolve.Exp003.Step5Controls.zero_generators_exact
#print axioms NDEAEvolve.Exp003.Step5Controls.zero_dimension_exact
#print axioms NDEAEvolve.Exp003.Step5Controls.negative_time_convergence
#print axioms NDEAEvolve.Exp003.Step5Controls.negative_time_bound
#print axioms NDEAEvolve.Exp003.Step5Controls.scalarCayley_matrix_entry
#print axioms NDEAEvolve.Exp003.Step5Controls.sign_reversal_detected
#print axioms NDEAEvolve.Exp003.Step5Controls.missing_halfstep_detected
#print axioms NDEAEvolve.Exp003.Step5Controls.finite_refinement_equality_rejected
#print axioms NDEAEvolve.Exp003.Step5Controls.finite_step_exponential_equality_rejected
