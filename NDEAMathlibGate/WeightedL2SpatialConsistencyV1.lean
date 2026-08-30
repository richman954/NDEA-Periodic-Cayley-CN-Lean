import NDEAMathlibGate.UniformVectorSpatialConsistencyV1

/-! Production V1: weighted discrete L2 spatial consistency. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEAWeightedL2SpatialConsistencyProbe

open NDEAPeriodicSamplingBridgeProbe
open NDEASampledSharpSpatialConsistencyProbe
open NDEAUniformVectorSpatialConsistencyProbe

abbrev VecState (n : ℕ) :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.VecState n

def sampledResidualEuclidean
    (L : ℝ) (u : ℝ → ℂ) (m : ℕ) : VecState (m + 1) :=
  WithLp.toLp 2 (sampledResidualVector L u m)

@[simp] theorem sampledResidualEuclidean_apply
    (L : ℝ) (u : ℝ → ℂ) (m : ℕ) (i : Fin (m + 1)) :
    WithLp.ofLp (sampledResidualEuclidean L u m) i =
      sampledResidualVector L u m i := by
  rfl

theorem sampledResidual_weightedNormSq_sharp
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
  let h := meshWidth L (m + 1)
  let B := M * h ^ 2 / 12
  have hh : 0 < h := meshWidth_pos_succ L m hL
  have hM : 0 ≤ M := (norm_nonneg _).trans (hderiv 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ i : Fin (m + 1),
      ‖sampledResidualVector L u m i‖ ^ 2 ≤ B ^ 2 := by
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _)
      (sampled_periodic_negLaplacian_spatial_consistency_sharp
        L hL u huPeriodic huC4 M hderiv i) 2
  unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
  rw [EuclideanSpace.norm_sq_eq]
  change h * ∑ i : Fin (m + 1),
      ‖sampledResidualVector L u m i‖ ^ 2 ≤ L * B ^ 2
  calc
    h * ∑ i : Fin (m + 1), ‖sampledResidualVector L u m i‖ ^ 2 ≤
        h * ∑ _i : Fin (m + 1), B ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _hi ↦ hpoint i) hh.le
    _ = L * B ^ 2 := by
      rw [Finset.sum_const, Finset.card_fin]
      rw [nsmul_eq_mul]
      have hcard : (((m + 1 : ℕ) : ℝ)) * h = L := by
        simpa [h] using card_mul_meshWidth_succ L m
      nlinarith

theorem sampledResidual_weightedNorm_sharp
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
  let h := meshWidth L (m + 1)
  let B := M * h ^ 2 / 12
  change NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
      h (sampledResidualEuclidean L u m) ≤ Real.sqrt L * B
  have hh : 0 ≤ h := (meshWidth_pos_succ L m hL).le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hderiv 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsquared := sampledResidual_weightedNormSq_sharp
    L hL u huPeriodic huC4 M hderiv m
  change NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
      h (sampledResidualEuclidean L u m) ≤ L * B ^ 2 at hsquared
  have hleft :=
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm_sq_eq
      h (sampledResidualEuclidean L u m) hh
  have hright : (Real.sqrt L * B) ^ 2 = L * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]
  have hnonneg : 0 ≤
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        h (sampledResidualEuclidean L u m) := by
    unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
    positivity
  have hrightNonneg : 0 ≤ Real.sqrt L * B := mul_nonneg (Real.sqrt_nonneg L) hB
  nlinarith [hleft, hright]

#check sampledResidual_weightedNormSq_sharp
#check sampledResidual_weightedNorm_sharp
#print axioms sampledResidual_weightedNormSq_sharp
#print axioms sampledResidual_weightedNorm_sharp

end NDEAWeightedL2SpatialConsistencyProbe
