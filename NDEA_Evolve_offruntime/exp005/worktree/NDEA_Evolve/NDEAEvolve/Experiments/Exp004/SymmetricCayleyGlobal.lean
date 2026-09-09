import NDEAEvolve.Experiments.Exp004.SymmetricCayleyLocal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Second-order global error for symmetric Cayley splitting

The finite-step estimate uses the already verified unitary telescoping fan.
At fixed physical time the cubic local error becomes an explicit inverse-square
step-count bound. Every norm is the induced continuous-linear-map norm.
-/

noncomputable section

open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004

/-- The symmetric Cayley step is unitary for every real step and every finite
dimension; there is no small-step or nonzero-dimension assumption. -/
theorem symmetricStepHat_mem_unitary {n : ℕ}
    (h : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    symmetricStepHat A B h ∈ unitary (E n →L[ℂ] E n) := by
  exact (unitary (E n →L[ℂ] E n)).mul_mem
    ((unitary (E n →L[ℂ] E n)).mul_mem
      (unitary_toEuclideanCLM (cayley_unitary (h / 4) A hA))
      (unitary_toEuclideanCLM (cayley_unitary (h / 2) B hB)))
    (unitary_toEuclideanCLM (cayley_unitary (h / 4) A hA))

/-- The finite telescoping identity, also valid for N=0. -/
theorem symmetric_cayley_exp_telescoping {n : ℕ}
    (h : ℝ) (A B : Mat n) (N : ℕ) :
    symmetricStepHat A B h ^ N - exactStepHat (A + B) (h / 2) ^ N =
      ∑ k ∈ Finset.range N,
        symmetricStepHat A B h ^ (N - 1 - k) *
          (symmetricStepHat A B h - exactStepHat (A + B) (h / 2)) *
          exactStepHat (A + B) (h / 2) ^ k :=
  pow_sub_pow_telescoping _ _ N

/-- Cubic local error accumulates at most linearly in the natural step count.
This all-N statement includes N=0 without a division convention. -/
theorem symmetric_cayley_exp_global_opNorm_le {n : ℕ}
    (h : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hstep : 2 * |h| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1) :
    ‖symmetricStepHat A B h ^ N - exactStepHat (A + B) (h / 2) ^ N‖ ≤
      (N : ℝ) * 1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 := by
  calc
    _ ≤ (N : ℝ) *
        ‖symmetricStepHat A B h - exactStepHat (A + B) (h / 2)‖ :=
      unitary_pow_sub_pow_opNorm_le _ _ N
        (symmetricStepHat_mem_unitary h A B hA hB)
        (exactStepHat_mem_unitary (h / 2) (A + B) (hA.add hB))
    _ ≤ (N : ℝ) *
        (1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (symmetric_cayley_exp_local_opNorm_le h A B hA hB hstep)
        (by positivity)
    _ = _ := by ring

/-- Explicit second-order global bound at fixed real physical time. The step
condition is eventually satisfied for every fixed time and pair of generators. -/
theorem symmetric_cayley_fixed_time_error_le {n : ℕ}
    (t : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ (N : ℝ)) :
    ‖symmetricStepHat A B (t / (N : ℝ)) ^ N -
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖ ≤
      1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have habs : |t / (N : ℝ)| = |t| / (N : ℝ) := by
    rw [abs_div, abs_of_pos hNr]
  have hs : 2 * |t / (N : ℝ)| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1 := by
    rw [habs]
    have hid : 2 * (|t| / (N : ℝ)) * (‖operatorOf A‖ + ‖operatorOf B‖) =
        (2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖)) / (N : ℝ) := by ring
    rw [hid]
    exact (div_le_one hNr).2 hstep
  have hb := symmetric_cayley_exp_global_opNorm_le
    (t / (N : ℝ)) A B N hA hB hs
  have hscale : t / (N : ℝ) / 2 = t / (2 * (N : ℝ)) := by ring
  rw [hscale, exactStepHat_fixed_time_pow t (A + B) N hN, habs] at hb
  convert hb using 1 <;> field_simp [hNr.ne'] <;> ring

/-- The explicit inverse-square majorant tends to zero. -/
theorem symmetric_cayley_fixed_time_majorant_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n) :
    Tendsto
      (fun N : ℕ =>
        1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds
      (x := 1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3)).mul
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)

/-- Operator-valued convergence of the error, including dimension zero. -/
theorem symmetric_cayley_fixed_time_difference_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        symmetricStepHat A B (t / (N : ℝ)) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (symmetric_cayley_fixed_time_majorant_tendsto_zero t A B)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖))] with N hN hstep
  exact symmetric_cayley_fixed_time_error_le t A B N hA hB hN hstep

/-- Symmetric Cayley powers converge to the exponential of the sum at each
fixed real time, without a step restriction on the convergence statement. -/
theorem symmetric_cayley_fixed_time_tendsto_exp {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun N : ℕ => symmetricStepHat A B (t / (N : ℝ)) ^ N)
      atTop
      (𝓝 (NormedSpace.exp
        ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))) := by
  exact tendsto_sub_nhds_zero_iff.mp
    (symmetric_cayley_fixed_time_difference_tendsto_zero t A B hA hB)

/-- The induced operator-norm error tends to zero. -/
theorem symmetric_cayley_fixed_time_error_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        ‖symmetricStepHat A B (t / (N : ℝ)) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (symmetric_cayley_fixed_time_difference_tendsto_zero t A B hA hB).norm

end NDEAEvolve.Exp004

#check @NDEAEvolve.Exp004.symmetric_cayley_exp_global_opNorm_le
#check @NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_le
#check @NDEAEvolve.Exp004.symmetric_cayley_fixed_time_tendsto_exp
#print axioms NDEAEvolve.Exp004.symmetricStepHat_mem_unitary
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_telescoping
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_global_opNorm_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_majorant_tendsto_zero
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_difference_tendsto_zero
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_tendsto_exp
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_tendsto_zero
