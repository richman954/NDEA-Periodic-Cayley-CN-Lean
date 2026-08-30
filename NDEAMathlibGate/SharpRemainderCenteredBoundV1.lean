import NDEAMathlibGate.TaylorIntervalGlobalBridgeV1
import NDEAMathlibGate.TaylorRemainderIntegrandBoundV1
import NDEAMathlibGate.SampledResidualIdentityV1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Production V1: sharp integral remainders and centered consistency bound. -/

noncomputable section

open Complex
open Set
open scoped BigOperators Interval

namespace NDEASharpRemainderAndCenteredBoundProbe

open NDEAIntervalToGlobalTaylorBridgeProbe
open NDEAAnalyticIntegrandBoundProbe
open NDEASampledResidualIdentityProbe

theorem plus_integrand_norm_bound_sharp
    (u : ℝ → ℂ) (x h M : ℝ)
    (hderiv : ∀ t ∈ Set.uIcc x (x + h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Set.uIoc x (x + h)) :
    ‖plusRemainderIntegrand u x h t‖ ≤
      (M / 6) * |t - (x + h)| ^ 3 := by
  have hd := hderiv t (Set.uIoc_subset_uIcc ht)
  have hcoeff :
      |(x + h - t) ^ 3 / (Nat.factorial 3 : ℝ)| =
        |t - (x + h)| ^ 3 / 6 := by
    rw [abs_div, abs_pow, abs_sub_comm]
    norm_num
  calc
    ‖plusRemainderIntegrand u x h t‖ =
        |(x + h - t) ^ 3 / (Nat.factorial 3 : ℝ)| *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ := by
            rw [plusRemainderIntegrand, norm_smul, Real.norm_eq_abs]
    _ = (|t - (x + h)| ^ 3 / 6) *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ := by rw [hcoeff]
    _ ≤ (|t - (x + h)| ^ 3 / 6) * M := by
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (M / 6) * |t - (x + h)| ^ 3 := by ring

theorem minus_integrand_norm_bound_sharp
    (u : ℝ → ℂ) (x h M : ℝ)
    (hderiv : ∀ t ∈ Set.uIcc x (x - h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Set.uIoc x (x - h)) :
    ‖minusRemainderIntegrand u x h t‖ ≤
      (M / 6) * |t - (x - h)| ^ 3 := by
  have hd := hderiv t (Set.uIoc_subset_uIcc ht)
  have hcoeff :
      |(x - h - t) ^ 3 / (Nat.factorial 3 : ℝ)| =
        |t - (x - h)| ^ 3 / 6 := by
    rw [abs_div, abs_pow, abs_sub_comm]
    norm_num
  calc
    ‖minusRemainderIntegrand u x h t‖ =
        |(x - h - t) ^ 3 / (Nat.factorial 3 : ℝ)| *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ := by
            rw [minusRemainderIntegrand, norm_smul, Real.norm_eq_abs]
    _ = (|t - (x - h)| ^ 3 / 6) *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ := by rw [hcoeff]
    _ ≤ (|t - (x - h)| ^ 3 / 6) * M := by
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (M / 6) * |t - (x - h)| ^ 3 := by ring

theorem remainderPlus_integral
    (u : ℝ → ℂ) (x h : ℝ) (hu : ContDiff ℝ 4 u) :
    remainderPlus u x h =
      ∫ t in x..x + h, plusRemainderIntegrand u x h t := by
  simpa [remainderPlus, taylorPlus, plusRemainderIntegrand] using
    (taylor_integral_remainder
      (f := u) (x := x + h) (x₀ := x) (n := 3) hu.contDiffOn)

theorem remainderMinus_integral
    (u : ℝ → ℂ) (x h : ℝ) (hu : ContDiff ℝ 4 u) :
    remainderMinus u x h =
      ∫ t in x..x - h, minusRemainderIntegrand u x h t := by
  simpa [remainderMinus, taylorMinus, minusRemainderIntegrand] using
    (taylor_integral_remainder
      (f := u) (x := x - h) (x₀ := x) (n := 3) hu.contDiffOn)

private theorem plus_kernel_integral
    (x h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M) :
    |∫ t in x..x + h, (M / 6) * |t - (x + h)| ^ 3| =
      M * h ^ 4 / 24 := by
  have hx : x ≤ x + h := by linarith
  rw [intervalIntegral.integral_of_le hx]
  rw [← Set.uIoc_of_le hx, Set.uIoc_comm]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_pow_abs_sub_uIoc]
  rw [show |x - (x + h)| = h by rw [abs_of_neg (by linarith)]; ring]
  rw [abs_of_nonneg (mul_nonneg (div_nonneg hM (by norm_num)) (by positivity))]
  ring

private theorem minus_kernel_integral
    (x h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M) :
    |∫ t in x..x - h, (M / 6) * |t - (x - h)| ^ 3| =
      M * h ^ 4 / 24 := by
  have hx : x - h ≤ x := by linarith
  rw [intervalIntegral.integral_of_ge hx]
  rw [← Set.uIoc_of_le hx]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_pow_abs_sub_uIoc]
  rw [show |x - (x - h)| = h by rw [abs_of_pos (by linarith)]; ring]
  rw [abs_neg]
  rw [abs_of_nonneg (mul_nonneg (div_nonneg hM (by norm_num)) (by positivity))]
  ring

theorem remainderPlus_norm_sharp
    (u : ℝ → ℂ) (x h M : ℝ) (hu : ContDiff ℝ 4 u) (hh : 0 < h)
    (hderiv : ∀ t ∈ Set.uIcc x (x + h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ ≤ M) :
    ‖remainderPlus u x h‖ ≤ M * h ^ 4 / 24 := by
  have hM : 0 ≤ M :=
    (norm_nonneg _).trans
      (hderiv (x + h) Set.right_mem_uIcc)
  have hg : IntervalIntegrable
      (fun t : ℝ ↦ (M / 6) * |t - (x + h)| ^ 3)
      MeasureTheory.volume x (x + h) :=
    (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.pow 3)).intervalIntegrable _ _
  have hae : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc x (x + h)),
      ‖plusRemainderIntegrand u x h t‖ ≤
        (M / 6) * |t - (x + h)| ^ 3 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun t ht ↦
      plus_integrand_norm_bound_sharp u x h M hderiv t ht
  rw [remainderPlus_integral u x h hu]
  calc
    ‖∫ t in x..x + h, plusRemainderIntegrand u x h t‖ ≤
        |∫ t in x..x + h, (M / 6) * |t - (x + h)| ^ 3| :=
      intervalIntegral.norm_integral_le_abs_of_norm_le hae hg
    _ = M * h ^ 4 / 24 := plus_kernel_integral x h M hh hM

theorem remainderMinus_norm_sharp
    (u : ℝ → ℂ) (x h M : ℝ) (hu : ContDiff ℝ 4 u) (hh : 0 < h)
    (hderiv : ∀ t ∈ Set.uIcc x (x - h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ ≤ M) :
    ‖remainderMinus u x h‖ ≤ M * h ^ 4 / 24 := by
  have hM : 0 ≤ M :=
    (norm_nonneg _).trans
      (hderiv (x - h) Set.right_mem_uIcc)
  have hg : IntervalIntegrable
      (fun t : ℝ ↦ (M / 6) * |t - (x - h)| ^ 3)
      MeasureTheory.volume x (x - h) :=
    (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.pow 3)).intervalIntegrable _ _
  have hae : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc x (x - h)),
      ‖minusRemainderIntegrand u x h t‖ ≤
        (M / 6) * |t - (x - h)| ^ 3 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun t ht ↦
      minus_integrand_norm_bound_sharp u x h M hderiv t ht
  rw [remainderMinus_integral u x h hu]
  calc
    ‖∫ t in x..x - h, minusRemainderIntegrand u x h t‖ ≤
        |∫ t in x..x - h, (M / 6) * |t - (x - h)| ^ 3| :=
      intervalIntegral.norm_integral_le_abs_of_norm_le hae hg
    _ = M * h ^ 4 / 24 := minus_kernel_integral x h M hh hM

theorem centered_remainder_assembly_sharp
    (rPlus rMinus : ℂ) (h M : ℝ) (hh : 0 < h)
    (hPlus : ‖rPlus‖ ≤ M * h ^ 4 / 24)
    (hMinus : ‖rMinus‖ ≤ M * h ^ 4 / 24) :
    ‖-(rPlus + rMinus) / (h : ℂ) ^ 2‖ ≤ M * h ^ 2 / 12 := by
  have hsum : ‖rPlus + rMinus‖ ≤ M * h ^ 4 / 12 := by
    calc
      ‖rPlus + rMinus‖ ≤ ‖rPlus‖ + ‖rMinus‖ := norm_add_le _ _
      _ ≤ M * h ^ 4 / 24 + M * h ^ 4 / 24 := add_le_add hPlus hMinus
      _ = M * h ^ 4 / 12 := by ring
  rw [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  apply (div_le_iff₀ hh2).2
  calc
    ‖rPlus + rMinus‖ ≤ M * h ^ 4 / 12 := hsum
    _ = (M * h ^ 2 / 12) * h ^ 2 := by ring

theorem centered_residual_norm_sharp
    (u : ℝ → ℂ) (x h M : ℝ) (hu : ContDiff ℝ 4 u) (hh : 0 < h)
    (hplusDeriv : ∀ t ∈ Set.uIcc x (x + h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ ≤ M)
    (hminusDeriv : ∀ t ∈ Set.uIcc x (x - h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ ≤ M) :
    ‖(2 * u x - u (x + h) - u (x - h)) / (h : ℂ) ^ 2 +
        iteratedDeriv 2 u x‖ ≤ M * h ^ 2 / 12 := by
  rw [centered_residual_eq_remainders u x h hu hh]
  exact centered_remainder_assembly_sharp
    (remainderPlus u x h) (remainderMinus u x h) h M hh
    (remainderPlus_norm_sharp u x h M hu hh hplusDeriv)
    (remainderMinus_norm_sharp u x h M hu hh hminusDeriv)

#check remainderPlus_norm_sharp
#check remainderMinus_norm_sharp
#check centered_residual_norm_sharp
#print axioms remainderPlus_norm_sharp
#print axioms remainderMinus_norm_sharp
#print axioms centered_residual_norm_sharp

end NDEASharpRemainderAndCenteredBoundProbe
