import SamplingExpansion
import PotentialAliasBounds

/-! Actual sampling and Fourier interpolation of Exp014 initial data.
The same physical period, grid sampler and weighted coefficient class are used.
An arbitrary discrepancy from exact nodal initialization remains explicit. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

private theorem isb_reconstruction_continuous (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) : Continuous (fourierReconstruction M h y) := by
  simpa only [fourierEval_apply] using
    (fourierEval_continuous M h).clm_apply (show Continuous (fun _ : ℝ => y) from continuous_const)

private theorem isb_synth_continuous (a : Exp014.FourierState (E 2)) :
    Continuous (Exp014.synth a) :=
  continuous_iff_continuousAt.mpr fun x => (Exp014.synth_hasDerivAt a x).continuousAt

/-- The actual interpolation error contains only frequencies beyond any resolved cutoff. -/
theorem sampledInitialState_error_norm_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    ‖fourierReconstruction M h (sampledInitialState M h a) x - Exp014.synth a x‖ ≤
      2 * frequencyNormTail (Exp014.coefficient a) R := by
  rw [sampledInitialState_reconstruction_sub_synth M h a x]
  have hs := frequencyNormTail_summable (Exp014.coefficient a)
    (Exp014.coefficient_summable_norm a) R
  apply tsum_of_norm_bounded (hs.hasSum.mul_left 2)
  intro ell
  by_cases he : (R : ℝ) < |(ell : ℝ)|
  · simp only [if_pos he]
    exact potentialModeDiscrepancy_norm_le M h hmesh ell _ x
  · have hm : |(ell : ℝ)| ≤ (M : ℝ) :=
      (le_of_not_gt he).trans (by exact_mod_cast hRM)
    rw [potentialModeDiscrepancy_eq_zero_of_memBand M h hmesh ell hm,
      norm_zero, if_neg he, mul_zero]

theorem sampledInitialState_spatialL2_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledInitialState M h a) x - Exp014.synth a x)
      b (2 * Real.pi) ≤ 2 * Real.sqrt (2 * Real.pi) *
        frequencyNormTail (Exp014.coefficient a) R := by
  exact (spatialL2_le_sqrt_mul_of_pointwise _
    ((isb_reconstruction_continuous M h _).sub (isb_synth_continuous a))
    (2 * frequencyNormTail (Exp014.coefficient a) R) b (2 * Real.pi)
    (mul_nonneg (by norm_num) (frequencyNormTail_nonneg _ _)) (by positivity)
    (sampledInitialState_error_norm_le_tail M R hRM h hmesh a)).trans_eq (by ring)

/-- The existing weighted state norm supplies the tail constant exactly. -/
theorem initialCoefficientTail_le_weighted (a : Exp014.FourierState (E 2)) (R : ℕ) :
    frequencyNormTail (Exp014.coefficient a) R ≤ ‖a‖ / (1 + (R : ℝ))^2 := by
  simpa only [Exp014.weighted_tsum_norm] using
    frequencyNormTail_le_weighted (Exp014.coefficient a)
      (Exp014.coefficient_summable_norm a) (Exp014.weighted_summable a) R

theorem sampledInitialState_spatialL2_le_weighted (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledInitialState M h a) x - Exp014.synth a x)
      b (2 * Real.pi) ≤ 2 * Real.sqrt (2 * Real.pi) * (‖a‖ / (1 + (M : ℝ))^2) :=
  (sampledInitialState_spatialL2_le_tail M M le_rfl h hmesh a b).trans
    (mul_le_mul_of_nonneg_left (initialCoefficientTail_le_weighted a M) (by positivity))

private theorem isb_reconstruction_norm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    ‖fourierReconstruction M h (sampledInitialState M h a) x‖ ≤
      ∑' ell : ℤ, ‖Exp014.coefficient a ell‖ := by
  rw [sampledInitialState_reconstruction_eq_tsum M h a x]
  apply tsum_of_norm_bounded (Exp014.coefficient_summable_norm a).hasSum
  intro ell
  exact (norm_fourierReconstruction_modeLift M h hmesh ell _ x).le

/-- Uniform physical-grid norm bound for actual nodal initialization, including aliases. -/
theorem sampledInitialState_weighted_norm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) :
    Real.sqrt h * ‖sampledInitialState M h a‖ ≤
      Real.sqrt (2 * Real.pi) * ∑' ell : ℤ, ‖Exp014.coefficient a ell‖ := by
  rw [← fourierReconstruction_spatialL2 M h hmesh _ 0]
  exact spatialL2_le_sqrt_mul_of_pointwise _ (isb_reconstruction_continuous M h _)
    _ 0 (2 * Real.pi) (tsum_nonneg (fun ell => norm_nonneg _)) (by positivity)
    (isb_reconstruction_norm_le M h hmesh a)

theorem sampledInitialState_weighted_norm_le_state (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) :
    Real.sqrt h * ‖sampledInitialState M h a‖ ≤ Real.sqrt (2 * Real.pi) * ‖a‖ := by
  apply (sampledInitialState_weighted_norm_le M h hmesh a).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [← Exp014.weighted_tsum_norm a]
  apply (Exp014.coefficient_summable_norm a).tsum_le_tsum _ (Exp014.weighted_summable a)
  intro ell
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (Exp014.weight_one_le ell) (norm_nonneg (Exp014.coefficient a ell))

/-- Arbitrary additional numerical initialization error retains its exact physical-grid norm. -/
theorem initialization_spatialL2_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (y : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => fourierReconstruction M h y x - Exp014.synth a x)
      b (2 * Real.pi) ≤ Real.sqrt h * ‖y - sampledInitialState M h a‖ +
        2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) R := by
  have ht := spatialL2_sub_triangle (fourierReconstruction M h y)
    (fourierReconstruction M h (sampledInitialState M h a)) (Exp014.synth a)
    b (2 * Real.pi) (by positivity) (isb_reconstruction_continuous M h y)
    (isb_reconstruction_continuous M h _) (isb_synth_continuous a)
  have he : (fun x => fourierReconstruction M h y x -
      fourierReconstruction M h (sampledInitialState M h a) x) =
      fourierReconstruction M h (y - sampledInitialState M h a) := by
    funext x
    simp only [← fourierEval_apply, map_sub]
  rw [he, fourierReconstruction_spatialL2 M h hmesh] at ht
  exact ht.trans (add_le_add le_rfl (sampledInitialState_spatialL2_le_tail M R hRM h hmesh a b))

theorem initialization_spatialL2_le_weighted (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (y : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => fourierReconstruction M h y x - Exp014.synth a x)
      b (2 * Real.pi) ≤ Real.sqrt h * ‖y - sampledInitialState M h a‖ +
        2 * Real.sqrt (2 * Real.pi) * (‖a‖ / (1 + (M : ℝ))^2) :=
  (initialization_spatialL2_le_tail M M le_rfl h hmesh a y b).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (initialCoefficientTail_le_weighted a M)
      (by positivity)))

#print axioms sampledInitialState_error_norm_le_tail
#print axioms sampledInitialState_spatialL2_le_tail
#print axioms initialCoefficientTail_le_weighted
#print axioms sampledInitialState_spatialL2_le_weighted
#print axioms sampledInitialState_weighted_norm_le
#print axioms sampledInitialState_weighted_norm_le_state
#print axioms initialization_spatialL2_le_tail
#print axioms initialization_spatialL2_le_weighted
end NDEAEvolve.Exp016
