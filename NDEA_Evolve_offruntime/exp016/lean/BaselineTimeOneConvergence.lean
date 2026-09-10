import SmoothCutoffConvergence
import InitialErrorTransfer

/-! Remove approximation cutoffs in the required order: fix the approximant,
take the actual mesh/time-step limit, then remove the approximation. This
reaches the original Exp014 initial-data/potential class at exact time 1.
Uniformity over all grid times and arbitrary finite horizons remain distinct.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
namespace NDEAEvolve.Exp016

/-- Uniform approximation costs can be removed after each approximant's limit. -/
theorem tendsto_zero_of_uniform_approximation (f : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hf : ∀ q, 0 ≤ f q) (hbound : ∀ R q, f q ≤ g R q + d R)
    (hg : ∀ R, Tendsto (g R) atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun q => lt_of_lt_of_le ha (hf q)
  · intro b hb
    obtain ⟨R, hR⟩ := ((tendsto_order.mp hd).2 (b / 2) (by linarith)).exists
    filter_upwards [(tendsto_order.mp (hg R)).2 (b / 2) (by linarith)] with q hq
    linarith [hbound R q]

/-- Fixed potential cutoff, original initial data, actual point initialization. -/
theorem scheduledCayley_potentialCutoff_error_tendsto_zero (R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q)
      (potentialCutoff R v) a (fun _ => temporalStepSize q) (temporalStepCount q) b 1)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_uniform_approximation _
    (fun S q => sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q)
      (potentialCutoff R v) (initialStateCutoff S a) (fun _ => temporalStepSize q)
      (temporalStepCount q) b 1)
    (fun S => 2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S)
  · intro q
    exact Exp015.spatialL2_nonneg _ _ _
  · intro S q
    exact sampledCayley_initialCutoff_error_transfer _ S _ (temporalSchedule_mesh q)
      (potentialCutoff R v) (potentialCutoff_regular R v) (potentialCutoff_hermitian R v hHerm)
      a (fun _ => temporalStepSize q) (temporalStepCount q) b 1 (by norm_num)
  · intro S
    exact scheduledCayley_doubleCutoff_error_tendsto_zero S R v hHerm a b
  · simpa only [mul_zero] using
      (frequencyNormTail_tendsto_zero (Exp014.coefficient a) (Exp014.coefficient_summable_norm a)
        (Exp014.weighted_summable a) id tendsto_id).const_mul (2 * Real.sqrt (2 * Real.pi))

/-- Original variable potential and original Exp014 datum, at the exact time 1. -/
theorem scheduledCayley_baseline_timeOne_error_tendsto_zero
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q)
      v a (fun _ => temporalStepSize q) (temporalStepCount q) b 1) atTop (𝓝 0) := by
  apply tendsto_zero_of_uniform_approximation _
    (fun R q => sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q)
      (potentialCutoff R v) a (fun _ => temporalStepSize q) (temporalStepCount q) b 1)
    (fun R => 2 * frequencyNormTail v R * (Real.sqrt (2 * Real.pi) * ‖a‖))
  · intro q
    exact Exp015.spatialL2_nonneg _ _ _
  · intro R q
    have he := sampledCayley_gridTime_cutoff_error_transfer _ R _ (temporalSchedule_mesh q)
      v hv hHerm a (fun _ => temporalStepSize q) (temporalStepCount q) b
      (fun _ _ => (temporalStepSize_pos q).le)
    rw [temporalSchedule_time_one] at he
    simpa only [mul_one] using he
  · intro R
    exact scheduledCayley_potentialCutoff_error_tendsto_zero R v hHerm a b
  · simpa only [mul_zero, zero_mul] using
      ((frequencyNormTail_tendsto_zero v (Exp014.regularPotential_absolute v hv) hv id tendsto_id)
        .const_mul 2).mul_const (Real.sqrt (2 * Real.pi) * ‖a‖)

#print axioms tendsto_zero_of_uniform_approximation
#print axioms scheduledCayley_potentialCutoff_error_tendsto_zero
#print axioms scheduledCayley_baseline_timeOne_error_tendsto_zero
end NDEAEvolve.Exp016
