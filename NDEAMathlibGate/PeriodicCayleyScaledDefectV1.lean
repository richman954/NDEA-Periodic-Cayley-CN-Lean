import NDEAMathlibGate.WeightedCayleyGlobalErrorV1

/-! Convert the normalized periodic space-time residual into a one-step defect. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicCayleyScaledDefectV1

open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1
open NDEAMathlibGate.WeightedCayleyGlobalErrorV1

def scaledDefect {n : ℕ} (k : ℝ) (residual : VecState n) : VecState n :=
  k • residual

theorem weightedNorm_scaledDefect {n : ℕ}
    (weight k : ℝ) (hk : 0 ≤ k) (residual : VecState n) :
    weightedNorm weight (scaledDefect k residual) =
      k * weightedNorm weight residual := by
  unfold weightedNorm scaledDefect
  unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk]
  ring

theorem periodic_scaled_spaceTime_defect_weightedNorm_bound
    (L : ℝ) (hL : 0 < L)
    (spatialProfile : ℝ → ℂ)
    (hPeriodic : Function.Periodic spatialProfile L)
    (hSpatialC4 : ContDiff ℝ 4 spatialProfile)
    (Ms : ℝ)
    (hSpatialDeriv : ∀ x : ℝ, ‖iteratedDeriv 4 spatialProfile x‖ ≤ Ms)
    (m : ℕ) (temporalResidual : Fin (m + 1) → ℂ)
    (k Mt : ℝ) (hk : 0 ≤ k) (hMt : 0 ≤ Mt)
    (hTemporal : ∀ i, ‖temporalResidual i‖ ≤ 5 * Mt * k ^ 2 / 12) :
    weightedNorm (meshWidth L (m + 1))
        (scaledDefect k
          (spaceTimeResidualEuclidean m temporalResidual L spatialProfile)) ≤
      k * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
        (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2) := by
  rw [weightedNorm_scaledDefect _ _ hk]
  apply mul_le_mul_of_nonneg_left _ hk
  calc
    weightedNorm (meshWidth L (m + 1))
        (spaceTimeResidualEuclidean m temporalResidual L spatialProfile) ≤
      Real.sqrt L *
        (5 * Mt * k ^ 2 / 12 +
          Ms * meshWidth L (m + 1) ^ 2 / 12) :=
      periodic_spaceTimeResidual_weightedNorm_bound
        L hL spatialProfile hPeriodic hSpatialC4 Ms hSpatialDeriv
          m temporalResidual k Mt hMt hTemporal
    _ = (Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
        (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2 := by ring

def scaledDefectStatus : String :=
  "normalized_residual_scaled_to_Ok3_plus_Okh2_additive_defect"

end NDEAMathlibGate.PeriodicCayleyScaledDefectV1
