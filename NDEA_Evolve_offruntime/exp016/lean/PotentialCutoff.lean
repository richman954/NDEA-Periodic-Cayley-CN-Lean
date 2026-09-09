import FourierTailBounds

/-! Symmetric finite Fourier cutoffs of the actual operator-valued potential.
The inclusive cutoff preserves Hermitian symmetry, and the complete omitted
coefficient mass is exactly the existing strict frequency tail. These are
potential-approximation estimates, without a time-stepping convergence claim.
-/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp016

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Retain precisely the symmetric inclusive Fourier band |ell| ≤ R. -/
def potentialCutoff (R : ℕ) (v : ℤ → H →L[ℂ] H) (ell : ℤ) : H →L[ℂ] H :=
  if |(ell : ℝ)| ≤ (R : ℝ) then v ell else 0

/-- Every finite cutoff is regular, even without regularity of the original series. -/
theorem potentialCutoff_regular (R : ℕ) (v : ℤ → H →L[ℂ] H) :
    Exp014.RegularPotential (potentialCutoff R v) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.Icc (-(R : ℤ)) (R : ℤ))
    (f := fun ell : ℤ => Exp014.weight ell * ‖potentialCutoff R v ell‖) ?_).summable
  intro ell hell
  have hn : ¬ |(ell : ℝ)| ≤ (R : ℝ) := by
    intro he
    have hz : |ell| ≤ (R : ℤ) := by exact_mod_cast he
    exact hell (Finset.mem_Icc.mpr (abs_le.mp hz))
  rw [potentialCutoff, if_neg hn, norm_zero, mul_zero]

/-- Symmetry of the retained band preserves the exact adjoint relation. -/
theorem potentialCutoff_hermitian (R : ℕ) (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.HermitianFourierPotential v) :
    Exp014.HermitianFourierPotential (potentialCutoff R v) := by
  intro ell
  simp only [potentialCutoff, Int.cast_neg, abs_neg]
  split_ifs <;> simp only [hv ell, star_zero]

/-- The coefficient difference has exactly the omitted absolute Fourier mass. -/
theorem potentialCutoff_difference_norm_sum (R : ℕ) (v : ℤ → H →L[ℂ] H) :
    (∑' ell : ℤ, ‖v ell - potentialCutoff R v ell‖) = frequencyNormTail v R := by
  unfold frequencyNormTail
  apply tsum_congr
  intro ell
  by_cases he : |(ell : ℝ)| ≤ (R : ℝ)
  · simp only [potentialCutoff, if_pos he, sub_self, norm_zero, if_neg (not_lt_of_ge he)]
  · simp only [potentialCutoff, if_neg he, sub_zero, if_pos (lt_of_not_ge he)]

/-- Uniform operator error is bounded by the actual omitted coefficient tail. -/
theorem operatorPotential_cutoff_norm_le_tail (R : ℕ) (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (x : ℝ) :
    ‖Exp014.operatorPotential v x - Exp014.operatorPotential (potentialCutoff R v) x‖ ≤
      frequencyNormTail v R := by
  have hs := (Exp014.operatorPotential_summable_norm v hv x).of_norm
  have hc := (Exp014.operatorPotential_summable_norm (potentialCutoff R v)
    (potentialCutoff_regular R v) x).of_norm
  unfold Exp014.operatorPotential
  rw [← hs.tsum_sub hc]
  apply tsum_of_norm_bounded
    (frequencyNormTail_summable v (Exp014.regularPotential_absolute v hv) R).hasSum
  intro ell
  by_cases he : |(ell : ℝ)| ≤ (R : ℝ)
  · simp only [potentialCutoff, if_pos he, sub_self, norm_zero, if_neg (not_lt_of_ge he), le_refl]
  · simp only [potentialCutoff, if_neg he, smul_zero, sub_zero, norm_smul,
      Exp014.character_norm, one_mul, if_pos (lt_of_not_ge he), le_refl]

/-- Exp014's existing weighted absolute coefficient norm controls the uniform error. -/
theorem operatorPotential_cutoff_norm_le_weighted (R : ℕ) (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (x : ℝ) :
    ‖Exp014.operatorPotential v x - Exp014.operatorPotential (potentialCutoff R v) x‖ ≤
      (∑' ell : ℤ, Exp014.weight ell * ‖v ell‖) / (1 + (R : ℝ)) ^ 2 :=
  (operatorPotential_cutoff_norm_le_tail R v hv x).trans
    (frequencyNormTail_le_weighted v (Exp014.regularPotential_absolute v hv) hv R)

#print axioms potentialCutoff
#print axioms potentialCutoff_regular
#print axioms potentialCutoff_hermitian
#print axioms potentialCutoff_difference_norm_sum
#print axioms operatorPotential_cutoff_norm_le_tail
#print axioms operatorPotential_cutoff_norm_le_weighted
end NDEAEvolve.Exp016
