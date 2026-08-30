import NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
import NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1

/-! Assembly of validated spatial and temporal local consistency bounds. -/

noncomputable section

open Complex Set

namespace NDEAMathlibGate.PeriodicCayleySpaceTimeLocalConsistencyV1

open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1
open NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1

def spaceTimeLocalResidual (temporalResidual spatialResidual : ℂ) : ℂ :=
  temporalResidual + spatialResidual

theorem spaceTimeLocalResidual_norm_bound
    (temporalResidual spatialResidual : ℂ)
    (k h Mt Ms : ℝ)
    (ht : ‖temporalResidual‖ ≤ 5 * Mt * k ^ 2 / 12)
    (hs : ‖spatialResidual‖ ≤ Ms * h ^ 2 / 12) :
    ‖spaceTimeLocalResidual temporalResidual spatialResidual‖ ≤
      5 * Mt * k ^ 2 / 12 + Ms * h ^ 2 / 12 := by
  calc
    ‖spaceTimeLocalResidual temporalResidual spatialResidual‖ ≤
        ‖temporalResidual‖ + ‖spatialResidual‖ := by
      exact norm_add_le _ _
    _ ≤ 5 * Mt * k ^ 2 / 12 + Ms * h ^ 2 / 12 :=
      add_le_add ht hs

theorem periodic_cayley_pointwise_spaceTime_consistency
    (L : ℝ) (hL : 0 < L)
    (spatialProfile : ℝ → ℂ)
    (hPeriodic : Function.Periodic spatialProfile L)
    (hSpatialC4 : ContDiff ℝ 4 spatialProfile)
    (Ms : ℝ)
    (hSpatialDeriv : ∀ x : ℝ, ‖iteratedDeriv 4 spatialProfile x‖ ≤ Ms)
    {m : ℕ} (i : Fin (m + 1))
    (trajectory dtrajectory : ℝ → ℂ) (t k Mt : ℝ) (hk : 0 < k)
    (hTrajectoryC3 : ContDiff ℝ 3 trajectory)
    (hDTrajectoryC2 : ContDiff ℝ 2 dtrajectory)
    (hdu0 : dtrajectory t = iteratedDeriv 1 trajectory t)
    (hdu1 : dtrajectory (t + k) = iteratedDeriv 1 trajectory (t + k))
    (hd2 : iteratedDeriv 1 dtrajectory t = iteratedDeriv 2 trajectory t)
    (hTrajectory3 : ∀ s ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 3 trajectory (Set.Icc t (t + k)) s‖ ≤ Mt)
    (hDTrajectory2 : ∀ s ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 2 dtrajectory (Set.Icc t (t + k)) s‖ ≤ Mt) :
    ‖spaceTimeLocalResidual
        (cnFunctionLocalDefect trajectory t k)
        ((NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
            (meshWidth L (m + 1)) (m + 1)).mulVec
              (sampleFixedPeriod L (m + 1) spatialProfile) i +
          iteratedDeriv 2 spatialProfile (gridPoint L (m + 1) i))‖ ≤
      5 * Mt * k ^ 2 / 12 +
        Ms * (meshWidth L (m + 1)) ^ 2 / 12 := by
  apply spaceTimeLocalResidual_norm_bound
  · exact cnFunctionLocalDefect_norm_bound_of_contDiff
      trajectory dtrajectory t k Mt hk hTrajectoryC3 hDTrajectoryC2
      hdu0 hdu1 hd2 hTrajectory3 hDTrajectory2
  · exact pointwise_spatial_consistency_sharp
      L hL spatialProfile hPeriodic hSpatialC4 Ms hSpatialDeriv i

def spaceTimeConsistencyStatus : String :=
  "periodic_spatial_Oh2_plus_crank_nicolson_temporal_Ok2_validated"

theorem spaceTimeConsistencyStatus_true :
    spaceTimeConsistencyStatus =
      "periodic_spatial_Oh2_plus_crank_nicolson_temporal_Ok2_validated" := rfl

end NDEAMathlibGate.PeriodicCayleySpaceTimeLocalConsistencyV1
