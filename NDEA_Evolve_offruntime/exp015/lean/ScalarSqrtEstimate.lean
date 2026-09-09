import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-! Sharp scalar square-root comparison for a nonnegative differentiable
energy. Positive regularization avoids dividing by an energy that may vanish.
The derivative itself need not be continuous. -/
noncomputable section
open MeasureTheory Set
namespace NDEAEvolve.Exp015

private theorem scalar_regularized_sqrt_bound
    (E D F : ℝ → ℝ) (hE : ∀ r, 0 ≤ E r)
    (hder : ∀ r, HasDerivAt E (D r) r)
    (hF : Continuous F) (hFnonneg : ∀ r, 0 ≤ F r)
    (hbound : ∀ r, D r ≤ 2 * Real.sqrt (E r) * F r)
    (s t : ℝ) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (E t + ε ^ 2) ≤
      Real.sqrt (E s + ε ^ 2) + ∫ r in s..t, F r := by
  have hpos (r : ℝ) : 0 < E r + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (hE r) (sq_pos_of_pos hε)
  have hd (r : ℝ) : HasDerivAt (fun x => Real.sqrt (E x + ε ^ 2))
      (D r / (2 * Real.sqrt (E r + ε ^ 2))) r :=
    ((hder r).add_const (ε ^ 2)).sqrt (hpos r).ne'
  have hcont : Continuous (fun r => Real.sqrt (E r + ε ^ 2)) :=
    continuous_iff_continuousAt.mpr fun r => (hd r).continuousAt
  have hmajor (r : ℝ) : D r / (2 * Real.sqrt (E r + ε ^ 2)) ≤ F r := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.mpr (hpos r)))).mpr
    have hsqrt : Real.sqrt (E r) ≤ Real.sqrt (E r + ε ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
    calc
      D r ≤ 2 * Real.sqrt (E r) * F r := hbound r
      _ ≤ 2 * Real.sqrt (E r + ε ^ 2) * F r :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (hFnonneg r)
      _ = F r * (2 * Real.sqrt (E r + ε ^ 2)) := by ring
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst
    hcont.continuousOn (fun r _ => (hd r).hasDerivWithinAt)
    hF.integrableOn_Icc (fun r _ => hmajor r)
  linarith

/-- A coefficient-one bound valid even when the energy vanishes. -/
theorem sqrt_energy_le_initial_add_integral
    (E D F : ℝ → ℝ) (hE : ∀ r, 0 ≤ E r)
    (hder : ∀ r, HasDerivAt E (D r) r)
    (hF : Continuous F) (hFnonneg : ∀ r, 0 ≤ F r)
    (hbound : ∀ r, D r ≤ 2 * Real.sqrt (E r) * F r)
    (s t : ℝ) (hst : s ≤ t) :
    Real.sqrt (E t) ≤ Real.sqrt (E s) + ∫ r in s..t, F r := by
  have hεbound (ε : ℝ) (hε : 0 < ε) :
      Real.sqrt (E t) ≤ Real.sqrt (E s) + (∫ r in s..t, F r) + ε := by
    have hreg := scalar_regularized_sqrt_bound E D F hE hder hF hFnonneg hbound s t hst ε hε
    have ht : Real.sqrt (E t) ≤ Real.sqrt (E t + ε ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
    have hs : Real.sqrt (E s + ε ^ 2) ≤ Real.sqrt (E s) + ε := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨add_nonneg (Real.sqrt_nonneg _) hε.le, ?_⟩
      nlinarith [Real.sq_sqrt (hE s), mul_nonneg (Real.sqrt_nonneg (E s)) hε.le]
    linarith
  by_contra h
  have hgap : 0 < Real.sqrt (E t) - (Real.sqrt (E s) + ∫ r in s..t, F r) := by
    linarith
  have he := hεbound ((Real.sqrt (E t) - (Real.sqrt (E s) + ∫ r in s..t, F r)) / 2)
    (half_pos hgap)
  linarith

end NDEAEvolve.Exp015
