import PotentialDefectExpansion
import FourierTailBounds

/-! Bounds for the actual sampled-potential spatial defect, including both
aliases in the retained band and the continuum product outside that band.
The computed high-frequency data tail is retained explicitly. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem potentialModeDiscrepancy_norm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (n : ℤ) (u : E 2) (x : ℝ) :
    ‖potentialModeDiscrepancy M h n u x‖ ≤ 2 * ‖u‖ := by
  unfold potentialModeDiscrepancy
  have hb := norm_sub_le (fourierReconstruction M h
    (Exp008.FourierGrid.modeLiftCLM (2 * M) h n u) x) (phase ((n : ℝ) * x) • u)
  rw [norm_fourierReconstruction_modeLift M h hmesh, norm_smul, phase_norm, one_mul] at hb
  exact hb.trans_eq (by ring)

theorem potentialModeDiscrepancy_eq_zero_of_memBand (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (n : ℤ) (hn : |(n : ℝ)| ≤ (M : ℝ)) (u : E 2) (x : ℝ) :
    potentialModeDiscrepancy M h n u x = 0 := by
  rw [potentialModeDiscrepancy, fourierReconstruction_phase_of_memBand M h hmesh n hn,
    sub_self]

/-- Only out-of-band products contribute; the entire convergent series is bounded. -/
theorem potentialModeDiscrepancy_tsum_norm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (n : ℤ) (u : E 2) (x : ℝ) :
    ‖∑' ell : ℤ, potentialModeDiscrepancy M h (ell + n) (v ell u) x‖ ≤
      2 * (shiftedFrequencyNormTail v M n * ‖u‖) := by
  have hs := shiftedFrequencyNormTail_summable v (Exp014.regularPotential_absolute v hv) M n
  apply tsum_of_norm_bounded ((hs.hasSum.mul_right ‖u‖).mul_left 2)
  intro ell
  by_cases he : (M : ℝ) < |((ell + n : ℤ) : ℝ)|
  · simp only [if_pos he]
    exact (potentialModeDiscrepancy_norm_le M h hmesh _ _ x).trans
      (mul_le_mul_of_nonneg_left ((v ell).le_opNorm u) (by norm_num))
  · rw [potentialModeDiscrepancy_eq_zero_of_memBand M h hmesh _ (le_of_not_gt he),
      norm_zero, if_neg he, zero_mul, mul_zero]

theorem sampledPotentialDefect_norm_le_tailBudget (M R : ℕ) (hRM : R ≤ M)
    (h : ℝ) (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (x : ℝ) :
    ‖sampledPotentialDefect M h v x y‖ ≤ 2 * potentialAliasTailBudget M h v y R := by
  rw [sampledPotentialDefect_eq_sum_tsum M h hmesh v hv x y]
  calc
    _ ≤ ∑ m : Fin (2 * M + 1),
        ‖∑' ell : ℤ, potentialModeDiscrepancy M h (ell + oddFrequency M m)
          (v ell (fourierCoefficient M h y m)) x‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin (2 * M + 1),
        2 * (shiftedFrequencyNormTail v M (oddFrequency M m) *
          ‖fourierCoefficient M h y m‖) := by
      apply Finset.sum_le_sum
      intro m _
      exact potentialModeDiscrepancy_tsum_norm_le M h hmesh v hv _ _ x
    _ = 2 * ∑ m : Fin (2 * M + 1),
        shiftedFrequencyNormTail v M (oddFrequency M m) * ‖fourierCoefficient M h y m‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (potential_shifted_tails_le_budget M R hRM h v hv y)
      (by norm_num)

/-- Physical L2 potential-interpolation error, with both cutoff tails explicit. -/
theorem sampledPotentialDefect_spatialL2_le_tailBudget (M R : ℕ) (hRM : R ≤ M)
    (h : ℝ) (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => sampledPotentialDefect M h v x y) b (2 * Real.pi) ≤
      2 * Real.sqrt (2 * Real.pi) * potentialAliasTailBudget M h v y R := by
  have hc : Continuous (fun x => sampledPotentialDefect M h v x y) :=
    (fourierRegularSynthesis M h).potentialDefect_apply_continuous _ _
      (Exp014.operatorPotential_continuous v hv) y
  exact (spatialL2_le_sqrt_mul_of_pointwise _ hc (2 * potentialAliasTailBudget M h v y R)
    b (2 * Real.pi) (mul_nonneg (by norm_num) (potentialAliasTailBudget_nonneg M h v y R))
    (by positivity) (sampledPotentialDefect_norm_le_tailBudget M R hRM h hmesh v hv y)).trans_eq
      (by ring)

/-- The potential tail rate uses the original second weighted absolute moment.
The numerical state's high-frequency tail still appears without a smallness claim. -/
theorem potentialAliasTailBudget_le_weighted (M R : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) :
    potentialAliasTailBudget M h v y R ≤
      ((∑' ell, Exp014.weight ell * ‖v ell‖) / (1 + ((M - R : ℕ) : ℝ)) ^ 2) *
        gridLowCoefficientNorm M h y R +
      (∑' ell, ‖v ell‖) * gridTailCoefficientNorm M h y R := by
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right
    (frequencyNormTail_le_weighted v (Exp014.regularPotential_absolute v hv) hv (M - R))
  unfold gridLowCoefficientNorm
  apply Finset.sum_nonneg
  intro m _; split_ifs <;> positivity

#print axioms potentialModeDiscrepancy_norm_le
#print axioms potentialModeDiscrepancy_eq_zero_of_memBand
#print axioms potentialModeDiscrepancy_tsum_norm_le
#print axioms sampledPotentialDefect_norm_le_tailBudget
#print axioms sampledPotentialDefect_spatialL2_le_tailBudget
#print axioms potentialAliasTailBudget_le_weighted
end NDEAEvolve.Exp016
