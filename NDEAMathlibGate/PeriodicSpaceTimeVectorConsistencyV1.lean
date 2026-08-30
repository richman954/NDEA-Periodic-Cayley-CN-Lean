import NDEAMathlibGate.PeriodicCayleySpaceTimeLocalConsistencyV1

/-! Weighted Euclidean lift of pointwise periodic space-time residual bounds. -/

noncomputable section

open Complex
open scoped BigOperators

namespace NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1

open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1

abbrev VecState (n : ℕ) :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.VecState n

def spaceTimeResidualEuclidean
    (m : ℕ) (temporalResidual : Fin (m + 1) → ℂ)
    (L : ℝ) (spatialProfile : ℝ → ℂ) : VecState (m + 1) :=
  WithLp.toLp 2 (fun i =>
    temporalResidual i + sampledResidualVector L spatialProfile m i)

theorem weightedNorm_of_pointwise_bound
    (L : ℝ) (hL : 0 < L) (r : Fin (m + 1) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hpoint : ∀ i, ‖r i‖ ≤ B) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1)) (WithLp.toLp 2 r) ≤ Real.sqrt L * B := by
  let h := meshWidth L (m + 1)
  have hh : 0 < h := NDEAPeriodicSamplingBridgeProbe.meshWidth_pos_succ L m hL
  have hsquared :
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
          h (WithLp.toLp 2 r) ≤ L * B ^ 2 := by
    unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
    rw [EuclideanSpace.norm_sq_eq]
    change h * ∑ i : Fin (m + 1), ‖r i‖ ^ 2 ≤ L * B ^ 2
    calc
      h * ∑ i : Fin (m + 1), ‖r i‖ ^ 2 ≤
          h * ∑ _i : Fin (m + 1), B ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hh.le
        apply Finset.sum_le_sum
        intro i _hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint i) 2
      _ = L * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hcard : (((m + 1 : ℕ) : ℝ)) * h = L := by
          simpa [h] using
            NDEAPeriodicSamplingBridgeProbe.card_mul_meshWidth_succ L m
        nlinarith
  have hleft :=
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm_sq_eq
      h (WithLp.toLp 2 r) hh.le
  have hright : (Real.sqrt L * B) ^ 2 = L * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]
  have hleftNonneg : 0 ≤
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        h (WithLp.toLp 2 r) := by
    unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
    positivity
  have hrightNonneg : 0 ≤ Real.sqrt L * B :=
    mul_nonneg (Real.sqrt_nonneg L) hB
  nlinarith

theorem periodic_spaceTimeResidual_weightedNorm_bound
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
        (spaceTimeResidualEuclidean m temporalResidual L spatialProfile) ≤
      Real.sqrt L *
        (5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12) := by
  have hMs : 0 ≤ Ms := (norm_nonneg _).trans (hSpatialDeriv 0)
  have hB : 0 ≤
      5 * Mt * k ^ 2 / 12 + Ms * meshWidth L (m + 1) ^ 2 / 12 := by
    positivity
  apply weightedNorm_of_pointwise_bound L hL _ _ hB
  intro i
  exact NDEAMathlibGate.PeriodicCayleySpaceTimeLocalConsistencyV1.spaceTimeLocalResidual_norm_bound
    (temporalResidual i) (sampledResidualVector L spatialProfile m i)
    k (meshWidth L (m + 1)) Mt Ms (hTemporal i)
    (pointwise_spatial_consistency_sharp L hL spatialProfile hPeriodic
      hSpatialC4 Ms hSpatialDeriv i)

def vectorConsistencyStatus : String :=
  "pointwise_space_time_residual_lifted_to_weighted_euclidean_norm"

end NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1
