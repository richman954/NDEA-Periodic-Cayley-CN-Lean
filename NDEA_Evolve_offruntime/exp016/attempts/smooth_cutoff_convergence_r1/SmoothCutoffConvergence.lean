import WeightedSlabSpatialBudget
import SpatialScalarRefinement

/-! Actual time-1 convergence for each fixed initial-data and potential cutoff.
The accumulated spatial residual is proved to vanish, using the actual
weighted trajectory estimate and its scalar coefficient limit. The error then
follows from the accepted Exp015/Exp014 certificate. This is an intermediate
smooth-approximation theorem, not yet the original-data, uniform-time target.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem scheduledSpatialSum_nonneg (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) :
    0 ≤ scheduledSpatialSum v a b q := by
  have hb (y : Vec (Grid (2 * initialSamplingCutoff q))) :
      0 ≤ sampledSpatialDefectBudget (initialSamplingCutoff q) (initialSamplingMesh q) v y b :=
    add_nonneg (Exp015.spatialL2_nonneg _ _ _) (Exp015.spatialL2_nonneg _ _ _)
  have hk := (temporalStepSize_pos q).le
  unfold scheduledSpatialSum
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg hk
  dsimp only [sampledSpatialStageBudget]
  exact add_nonneg (add_nonneg (hb _) (mul_nonneg (by positivity) (hb _)))
    (mul_nonneg (by positivity) (hb _))

/-- The actual sum vanishes; no residual-smallness premise is introduced. -/
theorem scheduledSpatialSum_doubleCutoff_tendsto_zero (S R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (scheduledSpatialSum (potentialCutoff R v) (initialStateCutoff S a) b)
      atTop (𝓝 0) := by
  have hc := spatialFourthWeightCoefficient_tendsto_zero (potentialCutoff R v)
    (potentialCutoff_regular R v)
  have hg := scheduledStep_generatorCoefficient_tendsto_zero (cutoffPotentialWeight 2 R v)
  have hm := (hc.mul ((hg.div_const 8).const_add 1)).mul_const
    (2 * (Real.exp (2 * (cutoffPotentialWeight 2 R v + 1)) * cutoffInitialWeight 2 S a))
  simp only [zero_div, add_zero, zero_mul] at hm
  exact squeeze_zero'
    (Eventually.of_forall (scheduledSpatialSum_nonneg (potentialCutoff R v) (initialStateCutoff S a) b))
    (scheduledSpatialSum_doubleCutoff_eventually_le S R v hHerm a b spatialLowCutoff spatialLowCutoff_le)
    hm

/-- Concrete solver convergence at exact time 1 for fixed finite cutoffs. -/
theorem scheduledCayley_doubleCutoff_error_tendsto_zero (S R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q)
      (potentialCutoff R v) (initialStateCutoff S a) (fun _ => temporalStepSize q)
      (temporalStepCount q) b 1) atTop (𝓝 0) := by
  have hz := (scheduledNonspatialBudget_tendsto_zero (potentialCutoff R v)
    (initialStateCutoff S a) b).add (scheduledSpatialSum_doubleCutoff_tendsto_zero S R v hHerm a b)
  simp only [add_zero] at hz
  apply squeeze_zero (fun q => Exp015.spatialL2_nonneg _ _ _) _ hz
  intro q
  simpa only [sampledCayleySolutionError, ← fourierReconstruction_eq_independentTarget] using
    scheduledCayley_error_le (potentialCutoff R v) (potentialCutoff_regular R v)
      (potentialCutoff_hermitian R v hHerm) (initialStateCutoff S a) b q

#print axioms scheduledSpatialSum_nonneg
#print axioms scheduledSpatialSum_doubleCutoff_tendsto_zero
#print axioms scheduledCayley_doubleCutoff_error_tendsto_zero
end NDEAEvolve.Exp016
