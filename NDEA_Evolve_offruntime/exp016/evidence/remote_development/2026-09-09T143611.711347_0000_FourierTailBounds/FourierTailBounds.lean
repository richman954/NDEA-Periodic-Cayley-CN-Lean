import SpatialDefectSplit

/-! Explicit absolute-frequency tails used by the actual potential alias bound.
The low band is inclusive and its tail is strict. No uniform numerical-state
tail bound is assumed. The potential rate uses exactly Exp014's existing weight. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def frequencyNormTail {F : Type*} [NormedAddCommGroup F] (f : ℤ → F) (R : ℕ) : ℝ :=
  ∑' j : ℤ, if (R : ℝ) < |(j : ℝ)| then ‖f j‖ else 0

def shiftedFrequencyNormTail {F : Type*} [NormedAddCommGroup F]
    (f : ℤ → F) (M : ℕ) (n : ℤ) : ℝ :=
  ∑' j : ℤ, if (M : ℝ) < |((j + n : ℤ) : ℝ)| then ‖f j‖ else 0

section Tails
variable {F : Type*} [NormedAddCommGroup F] (f : ℤ → F)
  (hf : Summable (fun j => ‖f j‖))

include hf in
theorem frequencyNormTail_summable (R : ℕ) :
    Summable (fun j : ℤ => if (R : ℝ) < |(j : ℝ)| then ‖f j‖ else 0) := by
  apply Summable.of_nonneg_of_le _ _ hf
  · intro j; split_ifs <;> positivity
  · intro j; split_ifs <;> simp [norm_nonneg]

include hf in
theorem shiftedFrequencyNormTail_summable (M : ℕ) (n : ℤ) :
    Summable (fun j : ℤ => if (M : ℝ) < |((j + n : ℤ) : ℝ)| then ‖f j‖ else 0) := by
  apply Summable.of_nonneg_of_le _ _ hf
  · intro j; split_ifs <;> positivity
  · intro j; split_ifs <;> simp [norm_nonneg]

theorem frequencyNormTail_nonneg (R : ℕ) : 0 ≤ frequencyNormTail f R := by
  apply tsum_nonneg
  intro j; split_ifs <;> positivity

theorem shiftedFrequencyNormTail_nonneg (M : ℕ) (n : ℤ) :
    0 ≤ shiftedFrequencyNormTail f M n := by
  apply tsum_nonneg
  intro j; split_ifs <;> positivity

include hf in
theorem shiftedFrequencyNormTail_le_total (M : ℕ) (n : ℤ) :
    shiftedFrequencyNormTail f M n ≤ ∑' j, ‖f j‖ := by
  apply (shiftedFrequencyNormTail_summable f hf M n).tsum_le_tsum _ hf
  intro j; split_ifs <;> simp [norm_nonneg]

/- Products of frequencies inside the two cutoffs remain represented. -/
include hf in
theorem shiftedFrequencyNormTail_le (M R : ℕ) (hRM : R ≤ M) (n : ℤ)
    (hn : |(n : ℝ)| ≤ (R : ℝ)) :
    shiftedFrequencyNormTail f M n ≤ frequencyNormTail f (M - R) := by
  apply (shiftedFrequencyNormTail_summable f hf M n).tsum_le_tsum _
    (frequencyNormTail_summable f hf (M - R))
  intro j
  by_cases hj : (M : ℝ) < |((j + n : ℤ) : ℝ)|
  · have htail : ((M - R : ℕ) : ℝ) < |(j : ℝ)| := by
      rw [Nat.cast_sub hRM]
      have ha : |((j + n : ℤ) : ℝ)| ≤ |(j : ℝ)| + |(n : ℝ)| := by
        simpa only [Int.cast_add] using abs_add_le (j : ℝ) (n : ℝ)
      linarith
    simp only [if_pos hj, if_pos htail, le_refl]
  · simp only [if_neg hj]
    split_ifs <;> positivity

/- The same second absolute moment already required by Exp014 bounds the tail. -/
include hf in
theorem frequencyNormTail_le_weighted (hw : Summable (fun j => Exp014.weight j * ‖f j‖))
    (R : ℕ) :
    frequencyNormTail f R ≤ (∑' j, Exp014.weight j * ‖f j‖) / (1 + (R : ℝ)) ^ 2 := by
  have hpos : 0 < (1 + (R : ℝ)) ^ 2 := by positivity
  apply (le_div_iff₀ hpos).mpr
  rw [mul_comm, frequencyNormTail, ← (frequencyNormTail_summable f hf R).tsum_mul_left]
  apply ((frequencyNormTail_summable f hf R).mul_left _).tsum_le_tsum _ hw
  intro j
  by_cases hj : (R : ℝ) < |(j : ℝ)|
  · rw [if_pos hj]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (by linarith : 1 + (R : ℝ) ≤ 1 + |(j : ℝ)|) 2
  · rw [if_neg hj, mul_zero]
    exact mul_nonneg (Exp014.weight_pos j).le (norm_nonneg _)
end Tails

def gridLowCoefficientNorm (M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) (R : ℕ) : ℝ :=
  ∑ m : Fin (2 * M + 1),
    if |(oddFrequency M m : ℝ)| ≤ (R : ℝ) then ‖fourierCoefficient M h y m‖ else 0

def gridTailCoefficientNorm (M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) (R : ℕ) : ℝ :=
  ∑ m : Fin (2 * M + 1),
    if |(oddFrequency M m : ℝ)| ≤ (R : ℝ) then 0 else ‖fourierCoefficient M h y m‖

def potentialAliasTailBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (R : ℕ) : ℝ :=
  frequencyNormTail v (M - R) * gridLowCoefficientNorm M h y R +
    (∑' j, ‖v j‖) * gridTailCoefficientNorm M h y R

theorem potentialAliasTailBudget_nonneg (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) (R : ℕ) :
    0 ≤ potentialAliasTailBudget M h v y R := by
  unfold potentialAliasTailBudget gridLowCoefficientNorm gridTailCoefficientNorm
  apply add_nonneg
  · apply mul_nonneg (frequencyNormTail_nonneg v _)
    apply Finset.sum_nonneg; intro m _; split_ifs <;> positivity
  · apply mul_nonneg (tsum_nonneg (fun j => norm_nonneg (v j)))
    apply Finset.sum_nonneg; intro m _; split_ifs <;> positivity

theorem potential_shifted_tails_le_budget (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) :
    (∑ m : Fin (2 * M + 1), shiftedFrequencyNormTail v M (oddFrequency M m) *
      ‖fourierCoefficient M h y m‖) ≤ potentialAliasTailBudget M h v y R := by
  unfold potentialAliasTailBudget gridLowCoefficientNorm gridTailCoefficientNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : |(oddFrequency M m : ℝ)| ≤ (R : ℝ)
  · simp only [if_pos hm, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right
      (shiftedFrequencyNormTail_le v (Exp014.regularPotential_absolute v hv) M R hRM _ hm)
      (norm_nonneg _)
  · simp only [if_neg hm, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_right
      (shiftedFrequencyNormTail_le_total v (Exp014.regularPotential_absolute v hv) M _)
      (norm_nonneg _)

/-- A uniform pointwise estimate implies the physical integral norm estimate. -/
theorem spatialL2_le_sqrt_mul_of_pointwise {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (u : ℝ → H) (hu : Continuous u)
    (C b L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hb : ∀ x, ‖u x‖ ≤ C) :
    Exp015.spatialL2 u b L ≤ Real.sqrt L * C := by
  have hi : (∫ x in b..b + L, ‖u x‖ ^ 2) ≤ L * C ^ 2 := by
    calc
      _ ≤ ∫ _x in b..b + L, C ^ 2 :=
        intervalIntegral.integral_mono (by linarith) ((hu.norm.pow 2).intervalIntegrable _ _)
          intervalIntegrable_const (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
      _ = _ := by simp
  exact (Real.sqrt_le_sqrt hi).trans_eq (by rw [Real.sqrt_mul hL, Real.sqrt_sq hC])

#print axioms shiftedFrequencyNormTail_le
#print axioms frequencyNormTail_le_weighted
#print axioms potential_shifted_tails_le_budget
#print axioms spatialL2_le_sqrt_mul_of_pointwise
end NDEAEvolve.Exp016
