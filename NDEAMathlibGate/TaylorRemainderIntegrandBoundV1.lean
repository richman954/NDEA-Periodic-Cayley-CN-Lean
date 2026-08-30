import NDEAMathlibGate.PeriodicLaplacian1DV1R2_ExplicitSBP
import Mathlib.Analysis.Calculus.Taylor

/-! Production V1: pointwise bounds for fourth-order Taylor integrands. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEAAnalyticIntegrandBoundProbe

def plusRemainderIntegrand (u : ℝ → ℂ) (x h t : ℝ) : ℂ :=
  ((x + h - t) ^ 3 / (Nat.factorial 3 : ℝ)) •
    iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t

def minusRemainderIntegrand (u : ℝ → ℂ) (x h t : ℝ) : ℂ :=
  ((x - h - t) ^ 3 / (Nat.factorial 3 : ℝ)) •
    iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t

theorem plus_integrand_norm_bound
    (u : ℝ → ℂ)
    (x h M : ℝ)
    (hh : 0 < h)
    (hderiv : ∀ t ∈ Set.uIcc x (x + h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ ≤ M)
    (t : ℝ)
    (ht : t ∈ Set.uIoc x (x + h)) :
    ‖plusRemainderIntegrand u x h t‖ ≤ M * h ^ 3 / 6 := by
  have ht' : t ∈ Set.Ioc x (x + h) := by
    rwa [Set.uIoc_of_le (by linarith : x ≤ x + h)] at ht
  have hk0 : 0 ≤ x + h - t := by linarith [ht'.2]
  have hkh : x + h - t ≤ h := by linarith [ht'.1]
  have hpow : (x + h - t) ^ 3 ≤ h ^ 3 :=
    pow_le_pow_left₀ hk0 hkh 3
  have hkernel :
      |(x + h - t) ^ 3 / (Nat.factorial 3 : ℝ)| ≤ h ^ 3 / 6 := by
    rw [abs_div, abs_pow, abs_of_nonneg hk0]
    norm_num
    exact div_le_div_of_nonneg_right hpow (by norm_num)
  have hd := hderiv t (Set.uIoc_subset_uIcc ht)
  calc
    ‖plusRemainderIntegrand u x h t‖ =
        |(x + h - t) ^ 3 / (Nat.factorial 3 : ℝ)| *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ := by
            rw [plusRemainderIntegrand, norm_smul, Real.norm_eq_abs]
    _ ≤ (h ^ 3 / 6) * M :=
      mul_le_mul hkernel hd (norm_nonneg _) (by positivity)
    _ = M * h ^ 3 / 6 := by ring

theorem minus_integrand_norm_bound
    (u : ℝ → ℂ)
    (x h M : ℝ)
    (hh : 0 < h)
    (hderiv : ∀ t ∈ Set.uIcc x (x - h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ ≤ M)
    (t : ℝ)
    (ht : t ∈ Set.uIoc x (x - h)) :
    ‖minusRemainderIntegrand u x h t‖ ≤ M * h ^ 3 / 6 := by
  have ht' : t ∈ Set.Ioc (x - h) x := by
    rwa [Set.uIoc_of_ge (by linarith : x - h ≤ x)] at ht
  have hk0 : 0 ≤ t - (x - h) := by linarith [ht'.1]
  have hkh : t - (x - h) ≤ h := by linarith [ht'.2]
  have hpow : (t - (x - h)) ^ 3 ≤ h ^ 3 :=
    pow_le_pow_left₀ hk0 hkh 3
  have hkernel :
      |(x - h - t) ^ 3 / (Nat.factorial 3 : ℝ)| ≤ h ^ 3 / 6 := by
    rw [abs_div, abs_pow, abs_of_nonpos (by linarith [ht'.1])]
    norm_num
    exact div_le_div_of_nonneg_right hpow (by norm_num)
  have hd := hderiv t (Set.uIoc_subset_uIcc ht)
  calc
    ‖minusRemainderIntegrand u x h t‖ =
        |(x - h - t) ^ 3 / (Nat.factorial 3 : ℝ)| *
          ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ := by
            rw [minusRemainderIntegrand, norm_smul, Real.norm_eq_abs]
    _ ≤ (h ^ 3 / 6) * M :=
      mul_le_mul hkernel hd (norm_nonneg _) (by positivity)
    _ = M * h ^ 3 / 6 := by ring

#check plus_integrand_norm_bound
#check minus_integrand_norm_bound
#print axioms plus_integrand_norm_bound
#print axioms minus_integrand_norm_bound

end NDEAAnalyticIntegrandBoundProbe
