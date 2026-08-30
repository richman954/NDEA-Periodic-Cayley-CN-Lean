import NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1
import NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1

/-! Weighted consistency for the Schrodinger-rotated space-time residual. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicRotatedSpaceTimeVectorConsistencyV1

open Complex
open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1
open NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1

def rotatedSpaceTimeResidualEuclidean
    (m : ℕ) (temporalResidual : Fin (m + 1) → ℂ)
    (L : ℝ) (spatialProfile : ℝ → ℂ) : VecState (m + 1) :=
  WithLp.toLp 2 (fun i =>
    temporalResidual i + Complex.I * sampledResidualVector L spatialProfile m i)

theorem periodic_sampled_factor_equation_euclidean
    (L k : ℝ) (hk : k ≠ 0) (m : ℕ)
    (uNowProfile uNextProfile : ℝ → ℂ)
    (duNow duNext : Fin (m + 1) → ℂ)
    (hPDEAverage : (2 : ℂ)⁻¹ • (duNext + duNow) =
      Complex.I • sampledSecondDerivative L (m + 1)
        (averageProfile uNowProfile uNextProfile)) :
    NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA (k / 2)
          (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
            (meshWidth L (m + 1)) (m + 1)))
        (WithLp.toLp 2 (sampleFixedPeriod L (m + 1) uNextProfile)) =
      NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction
          (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyB (k / 2)
            (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
              (meshWidth L (m + 1)) (m + 1)))
          (WithLp.toLp 2 (sampleFixedPeriod L (m + 1) uNowProfile)) +
        k • rotatedSpaceTimeResidualEuclidean m
          (NDEAMathlibGate.CayleySampledPDEFactorIdentityV1.cnResidualVector
            (sampleFixedPeriod L (m + 1) uNowProfile)
            (sampleFixedPeriod L (m + 1) uNextProfile) duNow duNext k)
          L (averageProfile uNowProfile uNextProfile) := by
  apply WithLp.ofLp_injective
  simpa [NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction,
    rotatedSpaceTimeResidualEuclidean] using
    periodic_sampled_factor_equation_raw L k hk m
      uNowProfile uNextProfile duNow duNext hPDEAverage

theorem periodic_rotated_spaceTimeResidual_weightedNorm_bound
    (L : ℝ) (hL : 0 < L)
    (spatialProfile : ℝ → ℂ)
    (hPeriodic : Function.Periodic spatialProfile L)
    (hSpatialC4 : ContDiff ℝ 4 spatialProfile)
    (Ms : ℝ)
    (hSpatialDeriv : ∀ x : ℝ, ‖iteratedDeriv 4 spatialProfile x‖ ≤ Ms)
    (m : ℕ) (temporalResidual : Fin (m + 1) → ℂ)
    (k Mt : ℝ) (hMt : 0 ≤ Mt)
    (hTemporal : ∀ i, ‖temporalResidual i‖ ≤ 5 * Mt * k ^ 2 / 12) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1))
        (rotatedSpaceTimeResidualEuclidean m temporalResidual L spatialProfile) ≤
      Real.sqrt L *
        (5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12) := by
  have hMs : 0 ≤ Ms := (norm_nonneg _).trans (hSpatialDeriv 0)
  have hB : 0 ≤
      5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12 := by
    positivity
  apply weightedNorm_of_pointwise_bound L hL _ _ hB
  intro i
  calc
    ‖temporalResidual i + Complex.I * sampledResidualVector L spatialProfile m i‖ ≤
        ‖temporalResidual i‖ +
          ‖Complex.I * sampledResidualVector L spatialProfile m i‖ := norm_add_le _ _
    _ = ‖temporalResidual i‖ +
          ‖sampledResidualVector L spatialProfile m i‖ := by simp
    _ ≤ 5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12 :=
      add_le_add (hTemporal i)
        (pointwise_spatial_consistency_sharp L hL spatialProfile hPeriodic
          hSpatialC4 Ms hSpatialDeriv i)

def rotatedVectorConsistencyStatus : String :=
  "schrodinger_rotated_space_time_residual_weighted_bound_validated"

end NDEAMathlibGate.PeriodicRotatedSpaceTimeVectorConsistencyV1
