import NDEAMathlibGate.PeriodicRotatedSpaceTimeVectorConsistencyV1
import NDEAMathlibGate.PeriodicCayleyScaledDefectV1

/-! Scale the Schrodinger-rotated normalized residual into a Cayley defect. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicRotatedCayleyScaledDefectV1

open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicRotatedSpaceTimeVectorConsistencyV1
open NDEAMathlibGate.PeriodicCayleyScaledDefectV1
open NDEAMathlibGate.WeightedCayleyGlobalErrorV1

theorem periodic_rotated_scaled_defect_weightedNorm_bound
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
          (rotatedSpaceTimeResidualEuclidean m temporalResidual L spatialProfile)) ≤
      k * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
        (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2) := by
  rw [weightedNorm_scaledDefect _ _ hk]
  apply mul_le_mul_of_nonneg_left _ hk
  calc
    weightedNorm (meshWidth L (m + 1))
        (rotatedSpaceTimeResidualEuclidean m temporalResidual L spatialProfile) ≤
      Real.sqrt L *
        (5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12) :=
      periodic_rotated_spaceTimeResidual_weightedNorm_bound
        L hL spatialProfile hPeriodic hSpatialC4 Ms hSpatialDeriv
          m temporalResidual k Mt hMt hTemporal
    _ = (Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
        (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2 := by ring

def rotatedScaledDefectStatus : String :=
  "rotated_factor_defect_Ok3_plus_Okh2_with_sharp_constants"

end NDEAMathlibGate.PeriodicRotatedCayleyScaledDefectV1
