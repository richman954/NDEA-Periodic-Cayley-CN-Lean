import SpatialL2

/-! Norm rules needed by actual reconstructed residuals and slab accumulation.
These apply to the existing integral-based spatialL2, without replacing it. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp016
open Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatialL2_smul (c : ℂ) (u : ℝ → H) (b L : ℝ) :
    spatialL2 (fun x => c • u x) b L = ‖c‖ * spatialL2 u b L := by
  unfold spatialL2
  simp_rw [norm_smul, mul_pow]
  rw [intervalIntegral.integral_const_mul, Real.sqrt_mul (sq_nonneg ‖c‖),
    Real.sqrt_sq (norm_nonneg c)]

theorem spatialL2_neg (u : ℝ → H) (b L : ℝ) :
    spatialL2 (fun x => -u x) b L = spatialL2 u b L := by
  simp only [spatialL2, norm_neg]

theorem spatialL2_add_le (u v : ℝ → H) (b L : ℝ) (hL : 0 ≤ L)
    (hu : Continuous u) (hv : Continuous v) :
    spatialL2 (fun x => u x + v x) b L ≤ spatialL2 u b L + spatialL2 v b L := by
  have hu2 : IntervalIntegrable (fun x => ‖u x‖ ^ 2) volume b (b + L) := (hu.norm.pow 2).intervalIntegrable b (b + L)
  have hv2 : IntervalIntegrable (fun x => ‖v x‖ ^ 2) volume b (b + L) := (hv.norm.pow 2).intervalIntegrable b (b + L)
  have huv : IntervalIntegrable (fun x => 2 * (‖u x‖ * ‖v x‖)) volume b (b + L) := ((hu.norm.mul hv.norm).const_mul 2).intervalIntegrable b (b + L)
  have hleft : IntervalIntegrable (fun x => ‖u x + v x‖ ^ 2) volume b (b + L) := ((hu.add hv).norm.pow 2).intervalIntegrable b (b + L)
  have hi : (∫ x in b..b+L, ‖u x + v x‖ ^ 2) ≤
      ∫ x in b..b+L, ‖u x‖ ^ 2 + 2 * (‖u x‖ * ‖v x‖) + ‖v x‖ ^ 2 := by
    apply intervalIntegral.integral_mono (by linarith) hleft ((hu2.add huv).add hv2)
    intro x
    have hn := norm_add_le (u x) (v x)
    nlinarith [norm_nonneg (u x + v x), norm_nonneg (u x), norm_nonneg (v x)]
  rw [intervalIntegral.integral_add (hu2.add huv) hv2,
    intervalIntegral.integral_add hu2 huv, intervalIntegral.integral_const_mul] at hi
  have hcs := norm_product_integral_le u v b L hL hu hv
  have hs : spatialL2 (fun x => u x + v x) b L ^ 2 ≤
      (spatialL2 u b L + spatialL2 v b L) ^ 2 := by
    rw [spatialL2_sq _ b L hL, add_sq, spatialL2_sq u b L hL, spatialL2_sq v b L hL]
    nlinarith
  exact le_of_sq_le_sq hs (add_nonneg (spatialL2_nonneg u b L) (spatialL2_nonneg v b L))

theorem spatialL2_sub_triangle (u v w : ℝ → H) (b L : ℝ) (hL : 0 ≤ L)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    spatialL2 (fun x => u x - w x) b L ≤
      spatialL2 (fun x => u x - v x) b L + spatialL2 (fun x => v x - w x) b L := by
  have h := spatialL2_add_le (fun x => u x - v x) (fun x => v x - w x)
    b L hL (hu.sub hv) (hv.sub hw)
  simpa only [sub_add_sub_cancel] using h

end NDEAEvolve.Exp016
