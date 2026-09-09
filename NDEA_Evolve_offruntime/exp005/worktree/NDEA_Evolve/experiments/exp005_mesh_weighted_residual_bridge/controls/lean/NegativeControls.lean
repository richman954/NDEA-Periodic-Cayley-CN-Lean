import NDEAEvolve.Experiments.Exp005.MeshFamilyConvergence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Focused controls for the conditional mesh bridge

These are positive compiled witnesses to actual false overclaims: norm
preservation alone does not imply consistency; a missing time-step factor
changes an accumulated error; a middle-stage residual cannot be discarded;
zero weight masks nonzero states; and two half Cayley steps are not generally
one full Cayley step. No claim about sharp rates or PDE consistency is inferred.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005.Controls

private theorem zero_step (n : ℕ) (k : ℝ) :
    symmetricStepHat (0 : Mat n) 0 k = (1 : E n →L[ℂ] E n) := by
  simp [symmetricStepHat, Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

private def spike : E 1 := PiLp.single 2 0 1

private theorem spike_norm : ‖spike‖ = 1 := by simp [spike]

private theorem spike_ne_zero : spike ≠ 0 := by
  intro h
  have hn := spike_norm
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The empty dimension is supported without norm(identity)=1. -/
theorem zero_dimension_weighted_error (dx : ℝ) (u v : E 0) :
    weightedNorm dx (u - v) = 0 := by
  have h : u - v = 0 := Subsingleton.elim _ _
  rw [h, weightedNorm_zero]

/-- The empty time interval has no measured defects. -/
theorem zero_count_certificate {n : ℕ} (dx k : ℝ) (A B : Mat n)
    (u v : ℕ → E n) :
    weightedNorm dx (u 0 - v 0) = weightedNorm dx (u 0 - v 0) +
      ∑ j ∈ Finset.range 0, weightedNorm dx (trajectoryDefect A B k u j) := by
  simp

/-- Zero physical time gives the identity, independently of generator size. -/
theorem zero_time_identity {n : ℕ} (A B : Mat n) :
    symmetricStepHat A B 0 = (1 : E n →L[ℂ] E n) := by
  simp [symmetricStepHat, Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

/-- Negative steps retain the stability property; convergence premises use
nonnegative time steps separately. -/
theorem negative_step_stability {n : ℕ} (dx : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (x : E n) :
    weightedNorm dx (symmetricStepHat A B (-1) x) = weightedNorm dx x :=
  symmetricStepHat_weightedNorm_preserved dx (-1) A B hA hB x

/-- Without positive weight, vanishing weighted error need not mean equality. -/
theorem zero_weight_masks_nonzero_state :
    ∃ x : E 1, x ≠ 0 ∧ weightedNorm 0 x = 0 := by
  exact ⟨spike, spike_ne_zero, by simp [weightedNorm]⟩

private def drift (k : ℝ) (j : ℕ) : E 1 := ((j : ℝ) * k) • spike

private theorem drift_defect (k : ℝ) (j : ℕ) :
    trajectoryDefect (0 : Mat 1) 0 k (drift k) j = k • spike := by
  rw [trajectoryDefect, zero_step]
  simp only [ContinuousLinearMap.one_apply, drift, ← sub_smul]
  congr 1
  push_cast
  ring

/-- A stable zero-generator scheme does not track an arbitrary drifting
reference: the actual residual is nonzero at every step. -/
theorem stability_alone_not_consistency :
    (∀ x : E 1, weightedNorm 1 (symmetricStepHat (0 : Mat 1) 0 1 x) =
      weightedNorm 1 x) ∧
    weightedNorm 1 (drift 1 2 - (0 : E 1)) = 2 ∧
    weightedNorm 1 (trajectoryDefect (0 : Mat 1) 0 1 (drift 1) 0) = 1 := by
  constructor
  · intro x
    rw [zero_step, ContinuousLinearMap.one_apply]
  · rw [drift_defect]
    norm_num [drift, weightedNorm, norm_smul, spike_norm]

/-- At N=2, k=1/2, T=1, each actual defect has size 1/2 but the error is 1.
Bounding a raw per-step defect by R only gives N*R, not T*R: the missing k
cannot be supplied by stability. The numerical trajectory is identically zero. -/
theorem missing_time_step_factor_detected :
    (∀ _j : ℕ, (0 : E 1) = symmetricStepHat (0 : Mat 1) 0 (1 / 2) 0) ∧
    (2 : ℝ) * (1 / 2) = 1 ∧
    (∀ j : ℕ, weightedNorm 1
      (trajectoryDefect (0 : Mat 1) 0 (1 / 2) (drift (1 / 2)) j) = 1 / 2) ∧
    weightedNorm 1 (drift (1 / 2) 0 - (0 : E 1)) + (1 : ℝ) * (1 / 2) <
      weightedNorm 1 (drift (1 / 2) 2 - (0 : E 1)) := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · intro j
    simp
  · intro j
    rw [drift_defect]
    norm_num [weightedNorm, norm_smul, spike_norm]
  · norm_num [drift, weightedNorm, norm_smul, spike_norm]

private theorem factorResidual_zero {n : ℕ} (alpha : ℝ) (x y : E n) :
    factorResidual (0 : Mat n) alpha x y = y - x := by
  simp [factorResidual, denominatorHat, numeratorHat, operatorOf,
    cayleyD, cayleyN, skewPart, cscalar]

/-- An exact positive witness rejects dropping the middle factor residual. -/
theorem omitted_middle_stage_detected :
    ∃ source first second target : E 1,
      factorResidual (0 : Mat 1) (1 / 4) source first = 0 ∧
      factorResidual (0 : Mat 1) (1 / 4) second target = 0 ∧
      weightedNorm 1 (factorResidual (0 : Mat 1) (1 / 2) first second) = 1 ∧
      0 < weightedNorm 1 (target - symmetricStepHat (0 : Mat 1) 0 1 source) := by
  refine ⟨0, 0, spike, spike, ?_⟩
  simp [factorResidual_zero, weightedNorm, spike_norm]

/-- Keeping all three residuals exactly accounts for the same witness. -/
theorem full_stage_budget_witness :
    stageResidualBudget 1 1 (0 : Mat 1) 0 0 0 spike spike = 1 := by
  simp [stageResidualBudget, factorResidual_zero, weightedNorm, spike_norm]

/-- Only the middle generator survives when A=0: this is one full CN step. -/
theorem middle_only_is_single_cayley {n : ℕ} (H : Mat n) (k : ℝ) :
    symmetricStepHat 0 H k = Chat H (k / 2) := by
  have hz : Chat (0 : Mat n) (k / 4) = 1 := by
    simp [Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]
  simp [symmetricStepHat, hz]

private def scalarCayley (alpha : ℝ) : ℂ :=
  (1 - Complex.I * (alpha : ℂ)) / (1 + Complex.I * (alpha : ℂ))

private theorem scalar_entry (alpha : ℝ) :
    cayley alpha (1 : Mat 1) 0 0 = scalarCayley alpha := by
  simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar,
    Matrix.mul_apply, Matrix.inv_subsingleton, Ring.inverse_eq_inv,
    scalarCayley, div_eq_mul_inv]

private theorem scalar_denominator (alpha : ℝ) : (1 + Complex.I * (alpha : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private theorem scalar_one : scalarCayley 1 = -Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator 1)).2
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

private theorem scalar_half : scalarCayley (1 / 2) = ((3 : ℂ) - 4 * Complex.I) / 5 := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator (1 / 2))).2
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

/-- The outer-only symmetric step is not the legacy single CN step.
At H=I and k=2, the respective scalar real parts are -7/25 and 0. -/
theorem outer_only_not_single_cayley :
    symmetricStepHat (1 : Mat 1) 0 2 ≠ Chat (1 : Mat 1) 1 := by
  intro h
  have hz : Chat (0 : Mat 1) ((2 : ℝ) / 2) = 1 := by
    simp [Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]
  have hquarter : (2 : ℝ) / 4 = 1 / 2 := by norm_num
  rw [symmetricStepHat, hz, mul_one, hquarter] at h
  have hm : cayley (1 / 2) (1 : Mat 1) * cayley (1 / 2) 1 = cayley 1 1 := by
    apply EquivLike.injective (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1))
    simpa only [Chat, map_mul] using h
  have he := congrFun (congrFun hm (0 : Fin 1)) (0 : Fin 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_one, scalar_entry] at he
  rw [scalar_half, scalar_one] at he
  have hre := congrArg Complex.re he
  norm_num [Complex.mul_re, Complex.mul_im] at hre

end NDEAEvolve.Exp005.Controls

#print axioms NDEAEvolve.Exp005.Controls.zero_dimension_weighted_error
#print axioms NDEAEvolve.Exp005.Controls.zero_count_certificate
#print axioms NDEAEvolve.Exp005.Controls.zero_time_identity
#print axioms NDEAEvolve.Exp005.Controls.negative_step_stability
#print axioms NDEAEvolve.Exp005.Controls.zero_weight_masks_nonzero_state
#print axioms NDEAEvolve.Exp005.Controls.stability_alone_not_consistency
#print axioms NDEAEvolve.Exp005.Controls.missing_time_step_factor_detected
#print axioms NDEAEvolve.Exp005.Controls.omitted_middle_stage_detected
#print axioms NDEAEvolve.Exp005.Controls.full_stage_budget_witness
#print axioms NDEAEvolve.Exp005.Controls.middle_only_is_single_cayley
#print axioms NDEAEvolve.Exp005.Controls.outer_only_not_single_cayley
