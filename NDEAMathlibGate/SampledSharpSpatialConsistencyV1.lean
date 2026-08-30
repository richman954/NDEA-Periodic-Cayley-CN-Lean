import NDEAMathlibGate.SharpRemainderCenteredBoundV1

/-! Production V1: sharp pointwise consistency on periodic sampled grids. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEASampledSharpSpatialConsistencyProbe

open NDEAPeriodicSamplingBridgeProbe
open NDEASharpRemainderAndCenteredBoundProbe

private theorem uniqueDiffOn_plus
    (x h : ℝ) (hh : 0 < h) :
    UniqueDiffOn ℝ (Set.uIcc x (x + h)) := by
  rw [Set.uIcc_of_le (by linarith)]
  exact uniqueDiffOn_Icc (by linarith)

private theorem uniqueDiffOn_minus
    (x h : ℝ) (hh : 0 < h) :
    UniqueDiffOn ℝ (Set.uIcc x (x - h)) := by
  rw [Set.uIcc_of_ge (by linarith : x - h ≤ x)]
  exact uniqueDiffOn_Icc (by linarith)

theorem global_fourth_deriv_bound_to_plus_interval
    (u : ℝ → ℂ) (x h M : ℝ) (hu : ContDiff ℝ 4 u) (hh : 0 < h)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M) :
    ∀ t ∈ Set.uIcc x (x + h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x + h)) t‖ ≤ M := by
  intro t ht
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_plus x h hh) hu.contDiffAt ht]
  exact hderiv t

theorem global_fourth_deriv_bound_to_minus_interval
    (u : ℝ → ℂ) (x h M : ℝ) (hu : ContDiff ℝ 4 u) (hh : 0 < h)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M) :
    ∀ t ∈ Set.uIcc x (x - h),
      ‖iteratedDerivWithin 4 u (Set.uIcc x (x - h)) t‖ ≤ M := by
  intro t ht
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_minus x h hh) hu.contDiffAt ht]
  exact hderiv t

theorem sampled_periodic_negLaplacian_spatial_consistency_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    {m : ℕ} (i : Fin (m + 1)) :
    ‖(NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
        (meshWidth L (m + 1)) (m + 1)).mulVec
          (sampleFixedPeriod L (m + 1) u) i +
        iteratedDeriv 2 u (gridPoint L (m + 1) i)‖ ≤
      M * (meshWidth L (m + 1)) ^ 2 / 12 := by
  rw [periodicNegLaplacian_sample_apply L u huPeriodic i]
  let x := gridPoint L (m + 1) i
  let h := meshWidth L (m + 1)
  have hh : 0 < h := meshWidth_pos_succ L m hL
  exact centered_residual_norm_sharp u x h M huC4 hh
    (global_fourth_deriv_bound_to_plus_interval u x h M huC4 hh hderiv)
    (global_fourth_deriv_bound_to_minus_interval u x h M huC4 hh hderiv)

#check sampled_periodic_negLaplacian_spatial_consistency_sharp
#print axioms sampled_periodic_negLaplacian_spatial_consistency_sharp

end NDEASampledSharpSpatialConsistencyProbe
