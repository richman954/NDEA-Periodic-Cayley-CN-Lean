import FiniteHorizonSpatial
import PotentialErrorTransfer

/-! One explicit residual-to-error certificate for every actual grid time
up to each fixed T>0. The temporal factor is exactly T³ times the saved
schedule bound; the complete actual spatial sum remains explicit. -/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

/-- Every prefix of the original ordered trajectory uses the same vanishing budget. -/
theorem horizonCayley_gridTime_error_le (T : ℝ) (hT : 0 < T) (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (q N : ℕ) (hN : N ≤ temporalStepCount q) :
    sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
      (fun _ => horizonStepSize T q) N b (actualCayleyTime (fun _ => horizonStepSize T q) N) ≤
        scheduledInitialError a b q + T^3 * scheduledTemporalBound v a q + horizonSpatialSum v a b T q := by
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := horizonStepSize T q
  let y := sampledInitialState M h a
  have hk : 0 < k := horizonStepSize_pos T hT q
  have he := sampledCayley_gridTime_explicitTemporal_error M h (temporalSchedule_mesh q)
    (temporalSchedule_mesh_pos q) v hv hHerm a y b (fun _ => k) N (fun _ _ => hk)
  have hcube : (∑ _j ∈ Finset.range N, k^3) ≤ T^3 * (temporalStepSize q)^2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (temporalStepCount q), k^3 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun _ _ _ => by positivity)
      _ = _ := horizonSchedule_sum_cube T q
  have hs : (∑ j ∈ Finset.range N, k * sampledSpatialStageBudget M h v
      (sampledCayleyTrajectory M h v y (fun _ => k) j) b k) ≤ horizonSpatialSum v a b T q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
    intro j _ _
    exact mul_nonneg hk.le (sampledSpatialStageBudget_nonneg M h v _ b k hk.le)
  have ht : (Real.sqrt h * ‖y‖) * physicalTemporalCoefficient h v *
      (∑ _j ∈ Finset.range N, k^3) ≤ T^3 * scheduledTemporalBound v a q := by
    calc
      _ ≤ (Real.sqrt h * ‖y‖) * physicalTemporalCoefficient h v * (T^3 * (temporalStepSize q)^2) :=
        mul_le_mul_of_nonneg_left hcube
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
            (physicalTemporalCoefficient_nonneg h v))
      _ ≤ (Real.sqrt (2 * Real.pi) * ‖a‖) * physicalTemporalCoefficient h v * (T^3 * (temporalStepSize q)^2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (sampledInitialState_weighted_norm_le_state M h (temporalSchedule_mesh q) a)
            (physicalTemporalCoefficient_nonneg h v)) (by positivity)
      _ = _ := by unfold scheduledTemporalBound; dsimp only [h, k]; ring
  have hf := he.trans (add_le_add (add_le_add le_rfl ht) hs)
  simpa only [sampledCayleySolutionError, ← fourierReconstruction_eq_independentTarget,
    scheduledInitialError] using hf


theorem horizonNonspatialBudget_tendsto_zero (T : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => scheduledInitialError a b q + T^3 * scheduledTemporalBound v a q)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun q => scheduledInitialError a b q) atTop (𝓝 0) := by
    simpa only [scheduledInitialError, ← fourierReconstruction_eq_independentTarget] using
      scheduledInitialSampling_spatialL2_tendsto_zero a b
  simpa only [mul_zero, add_zero] using hi.add ((scheduledTemporalBound_tendsto_zero v a).const_mul (T^3))

/-- All terms of the common prefix certificate vanish for each fixed approximant. -/
theorem horizonDoubleCutoffBudget_tendsto_zero (S R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => scheduledInitialError (initialStateCutoff S a) b q +
      T^3 * scheduledTemporalBound (potentialCutoff R v) (initialStateCutoff S a) q +
      horizonSpatialSum (potentialCutoff R v) (initialStateCutoff S a) b T q) atTop (𝓝 0) := by
  simpa only [add_zero] using
    (horizonNonspatialBudget_tendsto_zero T (potentialCutoff R v) (initialStateCutoff S a) b).add
      (horizonSpatialSum_doubleCutoff_tendsto_zero S R T hT v hHerm a b)

#print axioms horizonCayley_gridTime_error_le
#print axioms horizonNonspatialBudget_tendsto_zero
#print axioms horizonDoubleCutoffBudget_tendsto_zero
end NDEAEvolve.Exp016
