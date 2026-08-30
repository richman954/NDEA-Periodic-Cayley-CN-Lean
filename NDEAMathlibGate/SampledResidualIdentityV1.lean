import NDEAMathlibGate.TaylorIntervalGlobalBridgeV1
import NDEAMathlibGate.PeriodicSamplingBridgeV1

/-! Production V1: exact sampled centered-residual identity. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEASampledResidualIdentityProbe

open NDEAIntervalToGlobalTaylorBridgeProbe
open NDEAPeriodicSamplingBridgeProbe

def remainderPlus (u : ℝ → ℂ) (x h : ℝ) : ℂ :=
  u (x + h) - taylorPlus u x h

def remainderMinus (u : ℝ → ℂ) (x h : ℝ) : ℂ :=
  u (x - h) - taylorMinus u x h

theorem taylor_symmetric_degree3
    (u : ℝ → ℂ)
    (x h : ℝ)
    (hu : ContDiff ℝ 4 u)
    (hh : 0 < h) :
    taylorPlus u x h + taylorMinus u x h =
      2 * u x + (h : ℂ) ^ 2 * iteratedDeriv 2 u x := by
  rw [
    taylorPlus_eq_cubicOfFunction u x h hu hh,
    taylorMinus_eq_cubicOfFunction u x h hu hh
  ]
  unfold cubicOfFunction cubicGlobal
  simp
  ring

theorem centered_residual_eq_remainders
    (u : ℝ → ℂ)
    (x h : ℝ)
    (hu : ContDiff ℝ 4 u)
    (hh : 0 < h) :
    (2 * u x - u (x + h) - u (x - h)) / (h : ℂ) ^ 2 +
        iteratedDeriv 2 u x =
      -(remainderPlus u x h + remainderMinus u x h) / (h : ℂ) ^ 2 := by
  have hhc : (h : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hh
  unfold remainderPlus remainderMinus
  have hsum := taylor_symmetric_degree3 u x h hu hh
  field_simp [hhc]
  linear_combination -1 * hsum

theorem sampled_residual_eq_remainders
    (L : ℝ)
    (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    {m : ℕ}
    (i : Fin (m + 1)) :
    (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
      (meshWidth L (m + 1)) (m + 1)).mulVec
        (sampleFixedPeriod L (m + 1) u) i +
      iteratedDeriv 2 u (gridPoint L (m + 1) i) =
    -(remainderPlus u
          (gridPoint L (m + 1) i)
          (meshWidth L (m + 1)) +
        remainderMinus u
          (gridPoint L (m + 1) i)
          (meshWidth L (m + 1))) /
      (meshWidth L (m + 1) : ℂ) ^ 2 := by
  rw [periodicNegLaplacian_sample_apply L u huPeriodic i]
  exact centered_residual_eq_remainders
    u
    (gridPoint L (m + 1) i)
    (meshWidth L (m + 1))
    huC4
    (meshWidth_pos_succ L m hL)

#check centered_residual_eq_remainders
#check sampled_residual_eq_remainders
#print axioms centered_residual_eq_remainders
#print axioms sampled_residual_eq_remainders

end NDEASampledResidualIdentityProbe
