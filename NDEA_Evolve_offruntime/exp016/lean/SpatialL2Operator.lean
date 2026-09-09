import SpatialL2Bridge

/-! Pointwise norm domination and bounded multiplication for the unchanged
physical spatial L2 norm. The immediate consumer is the actual residual
created by changing a variable potential in an Exp014 solution. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp016
open Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatialL2_le_mul_of_norm_le (u v : ℝ → H)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖u x‖ ≤ C * ‖v x‖)
    (b L : ℝ) (hL : 0 ≤ L) :
    spatialL2 u b L ≤ C * spatialL2 v b L := by
  have hu2 : IntervalIntegrable (fun x => ‖u x‖ ^ 2) volume b (b + L) :=
    (hu.norm.pow 2).intervalIntegrable b (b + L)
  have hv2 : IntervalIntegrable (fun x => C ^ 2 * ‖v x‖ ^ 2) volume b (b + L) :=
    ((hv.norm.pow 2).const_mul (C ^ 2)).intervalIntegrable b (b + L)
  have hi : (∫ x in b..b+L, ‖u x‖ ^ 2) ≤
      ∫ x in b..b+L, C ^ 2 * ‖v x‖ ^ 2 := by
    apply intervalIntegral.integral_mono (by linarith) hu2 hv2
    intro x
    have hs := sq_le_sq₀ (norm_nonneg (u x)) (mul_nonneg hC (norm_nonneg (v x)))
    simpa only [mul_pow] using hs.mpr (hbound x)
  rw [intervalIntegral.integral_const_mul] at hi
  have hs : spatialL2 u b L ^ 2 ≤ (C * spatialL2 v b L) ^ 2 := by
    rw [mul_pow, spatialL2_sq _ b L hL, spatialL2_sq _ b L hL]
    exact hi
  exact le_of_sq_le_sq hs (mul_nonneg hC (spatialL2_nonneg v b L))

theorem spatialL2_operator_le (A : ℝ → H →L[ℂ] H) (u : ℝ → H)
    (hA : Continuous A) (hu : Continuous u)
    (δ : ℝ) (hδ : 0 ≤ δ) (hbound : ∀ x, ‖A x‖ ≤ δ)
    (b L : ℝ) (hL : 0 ≤ L) :
    spatialL2 (fun x => A x (u x)) b L ≤ δ * spatialL2 u b L := by
  exact spatialL2_le_mul_of_norm_le _ u (hA.clm_apply hu) hu δ hδ
    (fun x => (A x).le_of_opNorm_le (hbound x) (u x)) b L hL

#print axioms spatialL2_le_mul_of_norm_le
#print axioms spatialL2_operator_le

end NDEAEvolve.Exp016
