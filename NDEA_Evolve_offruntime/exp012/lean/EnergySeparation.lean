import Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Continuous spinor fields are separated by their nonnegative integral
energy. Allowing an arbitrary interval base covers every real spatial point
directly, including the left endpoint. -/
noncomputable section
open NDEAEvolve.Exp003
open MeasureTheory
namespace NDEAEvolve.Exp012

theorem norm_sq_integral_pos_of_ne_zero (f : ℝ → E 2) (hf : Continuous f)
    (b L : ℝ) (hL : 0 < L) (hb : f b ≠ 0) :
    0 < ∫ x in b..b+L, ‖f x‖^2 := by
  apply intervalIntegral.integral_pos (by linarith : b < b+L)
    (hf.norm.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · refine ⟨b, ⟨le_refl _, by linarith⟩, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem norm_sq_integrals_separate_zero (f : ℝ → E 2) (hf : Continuous f)
    (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖f x‖^2)=0) : f=0 := by
  funext x
  by_contra hx
  have hp := norm_sq_integral_pos_of_ne_zero f hf x L hL hx
  rw [hz x] at hp
  exact (lt_irrefl 0 hp)

theorem norm_sq_integrals_separate (f g : ℝ → E 2)
    (hf : Continuous f) (hg : Continuous g) (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖f x-g x‖^2)=0) : f=g := by
  have h := norm_sq_integrals_separate_zero (fun x => f x-g x) (hf.sub hg) L hL hz
  funext x
  exact sub_eq_zero.mp (congrFun h x)

end NDEAEvolve.Exp012
