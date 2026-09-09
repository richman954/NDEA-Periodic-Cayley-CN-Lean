import PotentialAliasBounds
import OneNodeCosine

/-! Exact resolved-product control for the actual sampled potential.
The potential and state bands are inclusive, and R+K=M is allowed. Finite
potential support supplies regularity; the computed alias-tail budget vanishes.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

private theorem aliasTail_regular_of_support (K : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : ∀ ell : ℤ, (K : ℝ) < |(ell : ℝ)| → v ell = 0) :
    Exp014.RegularPotential v := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) (K : ℤ))
    (f := fun ell : ℤ => Exp014.weight ell * ‖v ell‖) ?_).summable
  intro ell hell
  have htailZ : (K : ℤ) < |ell| := by
    by_contra hn
    exact hell (Finset.mem_Icc.mpr (abs_le.mp (le_of_not_gt hn)))
  have htail : (K : ℝ) < |(ell : ℝ)| := by exact_mod_cast htailZ
  rw [hv ell htail, norm_zero, mul_zero]

private theorem aliasTail_frequencyNormTail_zero (K L : ℕ) (hKL : K ≤ L)
    (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : ∀ ell : ℤ, (K : ℝ) < |(ell : ℝ)| → v ell = 0) :
    frequencyNormTail v L = 0 := by
  unfold frequencyNormTail
  have hz (ell : ℤ) : (if (L : ℝ) < |(ell : ℝ)| then ‖v ell‖ else 0) = 0 := by
    by_cases he : (L : ℝ) < |(ell : ℝ)|
    · have hKLr : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
      rw [if_pos he, hv ell (lt_of_le_of_lt hKLr he), norm_zero]
    · exact if_neg he
  simp only [hz, tsum_zero]

private theorem aliasTail_gridTail_zero (M R : ℕ) (h : ℝ) (y : Vec (Grid (2 * M)))
    (hy : ∀ m : Fin (2 * M + 1), (R : ℝ) < |(oddFrequency M m : ℝ)| →
      fourierCoefficient M h y m = 0) :
    gridTailCoefficientNorm M h y R = 0 := by
  unfold gridTailCoefficientNorm
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : |(oddFrequency M m : ℝ)| ≤ (R : ℝ)
  · exact if_pos hm
  · rw [if_neg hm, hy m (lt_of_not_ge hm), norm_zero]

private theorem aliasTail_budget_zero (M R K : ℕ) (hRK : R + K ≤ M) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : ∀ ell : ℤ, (K : ℝ) < |(ell : ℝ)| → v ell = 0)
    (y : Vec (Grid (2 * M)))
    (hy : ∀ m : Fin (2 * M + 1), (R : ℝ) < |(oddFrequency M m : ℝ)| →
      fourierCoefficient M h y m = 0) :
    potentialAliasTailBudget M h v y R = 0 := by
  unfold potentialAliasTailBudget
  rw [aliasTail_frequencyNormTail_zero K (M - R) (by omega) v hv,
    aliasTail_gridTail_zero M R h y hy, zero_mul, mul_zero, add_zero]

/-- The actual sampled product is exactly the continuum product whenever the
two inclusive frequency supports fit in the full resolved band. -/
theorem sampledPotential_product_exact_of_resolved_support (M R K : ℕ)
    (hRK : R + K ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : ∀ ell : ℤ, (K : ℝ) < |(ell : ℝ)| → v ell = 0)
    (y : Vec (Grid (2 * M)))
    (hy : ∀ m : Fin (2 * M + 1), (R : ℝ) < |(oddFrequency M m : ℝ)| →
      fourierCoefficient M h y m = 0) (x : ℝ) :
    fourierReconstruction M h (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y) x =
      Exp014.operatorPotential v x (fourierReconstruction M h y x) := by
  have hreg := aliasTail_regular_of_support K v hv
  have hn := sampledPotentialDefect_norm_le_tailBudget M R (by omega) h hmesh v hreg y x
  rw [aliasTail_budget_zero M R K hRK h v hv y hy, mul_zero] at hn
  have hz : sampledPotentialDefect M h v x y = 0 :=
    norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  rw [sampledPotentialDefect_apply] at hz
  exact sub_eq_zero.mp hz

namespace Controls

/-- Active Hermitian ±1 potential and nonzero +1 input mode on five nodes.
The product reaches frequency +2, exactly at the permitted boundary R+K=M. -/
theorem cosine_times_mode_one_resolved (x : ℝ) :
    let h := 2 * Real.pi / 5
    let y := modeLiftCLM 4 h 1 OneNodeCosine.spinor
    fourierReconstruction 2 h
      (op (sampledBlock 4 h (operatorPotentialMatrix OneNodeCosine.coefficients)) y) x =
      Exp014.operatorPotential OneNodeCosine.coefficients x (fourierReconstruction 2 h y x) := by
  dsimp only
  apply sampledPotential_product_exact_of_resolved_support 2 1 1 (by norm_num)
    (2 * Real.pi / 5) (by norm_num; ring) OneNodeCosine.coefficients
  · intro ell hell
    have hn : ¬ (ell = 1 ∨ ell = -1) := by
      rintro (rfl | rfl) <;> norm_num at hell
    exact if_neg hn
  · intro m hm
    change fourierCoefficient 2 (2 * Real.pi / 5)
      (modeLiftCLM 4 (2 * Real.pi / 5) (oddFrequency 2 ⟨3, by omega⟩)
        OneNodeCosine.spinor) m = 0
    rw [fourierCoefficient_modeLift 2 (2 * Real.pi / 5) (by norm_num; ring)]
    apply if_neg
    intro he
    subst m
    norm_num [oddFrequency] at hm

end Controls

#print axioms sampledPotential_product_exact_of_resolved_support
#print axioms Controls.cosine_times_mode_one_resolved
end NDEAEvolve.Exp016
