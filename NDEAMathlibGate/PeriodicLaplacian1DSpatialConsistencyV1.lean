import NDEAMathlibGate.WeightedL2SpatialConsistencyV1

/-!
# Periodic 1D negative-Laplacian spatial consistency

This module is the production facade for the validated degree-three Taylor
remainder chain. It exposes sharp pointwise, finite sup-norm, and weighted
discrete L2 consistency estimates for the periodic centered stencil.
-/

noncomputable section

open Complex

namespace NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1

open NDEAPeriodicSamplingBridgeProbe
open NDEASampledSharpSpatialConsistencyProbe
open NDEAUniformVectorSpatialConsistencyProbe
open NDEAWeightedL2SpatialConsistencyProbe

abbrev meshWidth := NDEAPeriodicSamplingBridgeProbe.meshWidth
abbrev gridPoint := NDEAPeriodicSamplingBridgeProbe.gridPoint
abbrev sampleFixedPeriod := NDEAPeriodicSamplingBridgeProbe.sampleFixedPeriod
abbrev sampledResidualVector :=
  NDEAUniformVectorSpatialConsistencyProbe.sampledResidualVector
abbrev sampledResidualEuclidean :=
  NDEAWeightedL2SpatialConsistencyProbe.sampledResidualEuclidean

theorem pointwise_spatial_consistency_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    {m : ℕ} (i : Fin (m + 1)) :
    ‖(NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
        (meshWidth L (m + 1)) (m + 1)).mulVec
          (sampleFixedPeriod L (m + 1) u) i +
        iteratedDeriv 2 u (gridPoint L (m + 1) i)‖ ≤
      M * (meshWidth L (m + 1)) ^ 2 / 12 := by
  exact sampled_periodic_negLaplacian_spatial_consistency_sharp
    L hL u huPeriodic huC4 M hderiv i

theorem supNorm_spatial_consistency_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    (m : ℕ) :
    ‖sampledResidualVector L u m‖ ≤
      M * (meshWidth L (m + 1)) ^ 2 / 12 := by
  exact sampledResidualVector_supNorm_sharp
    L hL u huPeriodic huC4 M hderiv m

theorem weightedL2Sq_spatial_consistency_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    (m : ℕ) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
        (meshWidth L (m + 1)) (sampledResidualEuclidean L u m) ≤
      L * (M * (meshWidth L (m + 1)) ^ 2 / 12) ^ 2 := by
  exact sampledResidual_weightedNormSq_sharp
    L hL u huPeriodic huC4 M hderiv m

theorem weightedL2_spatial_consistency_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    (m : ℕ) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1)) (sampledResidualEuclidean L u m) ≤
      Real.sqrt L * (M * (meshWidth L (m + 1)) ^ 2 / 12) := by
  exact sampledResidual_weightedNorm_sharp
    L hL u huPeriodic huC4 M hderiv m

def spatialConsistencyStatus : String :=
  "sharp_periodic_1d_pointwise_supnorm_weightedL2_validated"

theorem spatialConsistencyStatus_true :
    spatialConsistencyStatus =
      "sharp_periodic_1d_pointwise_supnorm_weightedL2_validated" := rfl

end NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
