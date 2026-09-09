import QuadraticTime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Pointwise and integrated norms for the actual quadratic operator residual.
The integral uses the exact polynomial coefficient and retains the full
endpoint defect. No smallness, selfadjointness or refinement assumption is used. -/
noncomputable section
open MeasureTheory Set

namespace NDEAEvolve.Exp016

theorem quadraticOffset_abs_le (t₀ k t : ℝ) (ht : t ∈ Icc t₀ (t₀ + k)) :
    |quadraticOffset t₀ k t| ≤ k / 2 := by
  apply abs_le.mpr
  constructor <;> dsimp only [quadraticOffset] <;> linarith [ht.1, ht.2]

theorem quadraticCorrection_continuous (t₀ k : ℝ) :
    Continuous (quadraticCorrection t₀ k) := by
  have h : Differentiable ℝ (quadraticCorrection t₀ k) :=
    fun t => (quadraticCorrection_hasDerivAt t₀ k t).differentiableAt
  exact h.continuous

theorem quadraticCorrection_norm_eq_on_slab (t₀ k t : ℝ)
    (ht : t ∈ Icc t₀ (t₀ + k)) :
    ‖quadraticCorrection t₀ k t‖ = (k ^ 2 / 4 - quadraticOffset t₀ k t ^ 2) / 2 := by
  have hb := abs_le.mp (quadraticOffset_abs_le t₀ k t ht)
  have hs : quadraticOffset t₀ k t ^ 2 ≤ k ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hb.1)]
  have hc : (quadraticOffset t₀ k t : ℂ) ^ 2 - (k : ℂ) ^ 2 / 4 =
      ((quadraticOffset t₀ k t ^ 2 - k ^ 2 / 4 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_ofNat]
  rw [quadraticCorrection, norm_mul, norm_div, Complex.norm_I, Complex.norm_ofNat,
    hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hs)]
  ring

theorem quadraticCorrection_norm_le (t₀ k t : ℝ) (ht : t ∈ Icc t₀ (t₀ + k)) :
    ‖quadraticCorrection t₀ k t‖ ≤ k ^ 2 / 8 := by
  rw [quadraticCorrection_norm_eq_on_slab t₀ k t ht]
  nlinarith [sq_nonneg (quadraticOffset t₀ k t)]

private theorem quadratic_norm_polynomial_integral (t₀ k : ℝ) :
    (∫ t in t₀..t₀ + k, (k ^ 2 / 4 - quadraticOffset t₀ k t ^ 2) / 2) =
      k ^ 3 / 12 := by
  let c : ℝ := t₀ + k / 2
  have hd (x : ℝ) :
      HasDerivAt (fun t : ℝ => (k ^ 2 / 8) * t - (t - c) ^ 3 / 6)
        ((k ^ 2 / 4 - (x - c) ^ 2) / 2) x := by
    have h := ((hasDerivAt_id x).const_mul (k ^ 2 / 8)).sub
      ((((hasDerivAt_id x).sub_const c).pow 3).div_const 6)
    have he : (k ^ 2 / 8) * 1 - (3 * (x - c) ^ (3 - 1) * 1) / 6 =
        (k ^ 2 / 4 - (x - c) ^ 2) / 2 := by ring
    simpa only [id_eq, Nat.cast_ofNat, he, Pi.pow_apply] using! h
  have hc : Continuous (fun t : ℝ => (k ^ 2 / 4 - (t - c) ^ 2) / 2) :=
    (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)).div_const 2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t₀) (b := t₀ + k) (fun x _ => hd x) (hc.intervalIntegrable _ _)
  calc
    (∫ t in t₀..t₀ + k, (k ^ 2 / 4 - quadraticOffset t₀ k t ^ 2) / 2) =
        ((k ^ 2 / 8) * (t₀ + k) - (t₀ + k - c) ^ 3 / 6) -
          ((k ^ 2 / 8) * t₀ - (t₀ - c) ^ 3 / 6) := by
      simpa only [quadraticOffset, c] using! hi
    _ = k ^ 3 / 12 := by dsimp only [c]; ring

theorem quadraticCorrection_integral_norm (t₀ k : ℝ) (hk : 0 ≤ k) :
    (∫ t in t₀..t₀ + k, ‖quadraticCorrection t₀ k t‖) = k ^ 3 / 12 := by
  have hle : t₀ ≤ t₀ + k := by linarith
  calc
    (∫ t in t₀..t₀ + k, ‖quadraticCorrection t₀ k t‖) =
        ∫ t in t₀..t₀ + k, (k ^ 2 / 4 - quadraticOffset t₀ k t ^ 2) / 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact quadraticCorrection_norm_eq_on_slab t₀ k t
        (by simpa only [uIcc_of_le hle] using ht)
    _ = k ^ 3 / 12 := quadratic_norm_polynomial_integral t₀ k

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem quadraticTime_gridResidual_norm_le (H : E →L[ℂ] E) (m v : E)
    (t₀ k t : ℝ) (ht : t ∈ Icc t₀ (t₀ + k)) :
    ‖Complex.I • deriv (quadraticTime H m v t₀ k) t - H (quadraticTime H m v t₀ k t)‖ ≤
      ‖Complex.I • v - H m‖ + (k ^ 2 / 8) * ‖H (H v)‖ := by
  rw [quadraticTime_gridResidual]
  calc
    ‖(Complex.I • v - H m) + quadraticCorrection t₀ k t • H (H v)‖ ≤
        ‖Complex.I • v - H m‖ + ‖quadraticCorrection t₀ k t • H (H v)‖ :=
      norm_add_le _ _
    _ = ‖Complex.I • v - H m‖ + ‖quadraticCorrection t₀ k t‖ * ‖H (H v)‖ := by
      rw [norm_smul]
    _ ≤ ‖Complex.I • v - H m‖ + (k ^ 2 / 8) * ‖H (H v)‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (quadraticCorrection_norm_le t₀ k t ht) (norm_nonneg _))

theorem quadraticTime_integral_gridResidual_norm_le (H : E →L[ℂ] E) (m v : E)
    (t₀ k : ℝ) (hk : 0 ≤ k) :
    (∫ t in t₀..t₀ + k,
      ‖Complex.I • deriv (quadraticTime H m v t₀ k) t - H (quadraticTime H m v t₀ k t)‖) ≤
        k * ‖Complex.I • v - H m‖ + (k ^ 3 / 12) * ‖H (H v)‖ := by
  have hle : t₀ ≤ t₀ + k := by linarith
  have hc := quadraticCorrection_continuous t₀ k
  have hleft : Continuous (fun t : ℝ =>
      ‖(Complex.I • v - H m) + quadraticCorrection t₀ k t • H (H v)‖) :=
    (continuous_const.add (hc.smul continuous_const)).norm
  have hconst : IntervalIntegrable (fun _ : ℝ => ‖Complex.I • v - H m‖)
      volume t₀ (t₀ + k) := continuous_const.intervalIntegrable _ _
  have hmul : IntervalIntegrable
      (fun t : ℝ => ‖quadraticCorrection t₀ k t‖ * ‖H (H v)‖)
      volume t₀ (t₀ + k) := (hc.norm.mul continuous_const).intervalIntegrable _ _
  calc
    (∫ t in t₀..t₀ + k,
      ‖Complex.I • deriv (quadraticTime H m v t₀ k) t - H (quadraticTime H m v t₀ k t)‖) =
        ∫ t in t₀..t₀ + k,
          ‖(Complex.I • v - H m) + quadraticCorrection t₀ k t • H (H v)‖ := by
      simp only [quadraticTime_gridResidual]
    _ ≤ ∫ t in t₀..t₀ + k,
        ‖Complex.I • v - H m‖ + ‖quadraticCorrection t₀ k t‖ * ‖H (H v)‖ := by
      apply intervalIntegral.integral_mono_on hle (hleft.intervalIntegrable _ _)
        (hconst.add hmul)
      intro t _
      simpa only [norm_smul] using
        norm_add_le (Complex.I • v - H m) (quadraticCorrection t₀ k t • H (H v))
    _ = k * ‖Complex.I • v - H m‖ + (k ^ 3 / 12) * ‖H (H v)‖ := by
      rw [intervalIntegral.integral_add hconst hmul, intervalIntegral.integral_const,
        intervalIntegral.integral_mul_const, quadraticCorrection_integral_norm t₀ k hk]
      simp only [add_sub_cancel_left, smul_eq_mul]

theorem quadraticSlab_gridResidual_norm_le (H : E →L[ℂ] E) (u₀ u₁ : E)
    (t₀ k t : ℝ) (ht : t ∈ Icc t₀ (t₀ + k)) :
    ‖Complex.I • deriv (quadraticSlab H u₀ u₁ t₀ k) t - H (quadraticSlab H u₀ u₁ t₀ k t)‖ ≤
      ‖Complex.I • quadraticVelocity u₀ u₁ k - H (quadraticMean u₀ u₁)‖ +
        (k ^ 2 / 8) * ‖H (H (quadraticVelocity u₀ u₁ k))‖ :=
  quadraticTime_gridResidual_norm_le H (quadraticMean u₀ u₁)
    (quadraticVelocity u₀ u₁ k) t₀ k t ht

theorem quadraticSlab_integral_gridResidual_norm_le (H : E →L[ℂ] E) (u₀ u₁ : E)
    (t₀ k : ℝ) (hk : 0 ≤ k) :
    (∫ t in t₀..t₀ + k,
      ‖Complex.I • deriv (quadraticSlab H u₀ u₁ t₀ k) t - H (quadraticSlab H u₀ u₁ t₀ k t)‖) ≤
        k * ‖Complex.I • quadraticVelocity u₀ u₁ k - H (quadraticMean u₀ u₁)‖ +
          (k ^ 3 / 12) * ‖H (H (quadraticVelocity u₀ u₁ k))‖ :=
  quadraticTime_integral_gridResidual_norm_le H (quadraticMean u₀ u₁)
    (quadraticVelocity u₀ u₁ k) t₀ k hk

end NDEAEvolve.Exp016
