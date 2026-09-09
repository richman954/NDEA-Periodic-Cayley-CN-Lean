import NDEAEvolve.Experiments.Exp003.ExactSplitUnsplitCayleyDefect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite-step telescoping bound for split Cayley evolution

This Step-4 module proves the noncommutative finite telescoping identity and
uses unitary left/right norm invariance together with the Step-3 local estimate
to obtain the global `N`-step induced operator-norm bound. No limit or
continuous-exponential comparison is used.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

/-! ## Noncommutative algebraic fan identity -/

/-- The ordered power-difference telescoping identity in an arbitrary ring.
The natural subtractions in the exponent are valid on `Finset.range N`; the
statement also covers `N = 0`. -/
theorem pow_sub_pow_telescoping {R₀ : Type*} [Ring R₀]
    (S U : R₀) (N : ℕ) :
    S ^ N - U ^ N =
      ∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k := by
  let f : ℕ → R₀ := fun k => S ^ (N - k) * U ^ k
  calc
    S ^ N - U ^ N = f 0 - f N := by simp [f]
    _ = ∑ k ∈ Finset.range N, (f k - f (k + 1)) :=
      (Finset.sum_range_sub' f N).symm
    _ = ∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < N := Finset.mem_range.mp hk
      have hleft : N - k = (N - 1 - k) + 1 := by omega
      have hright : N - (k + 1) = N - 1 - k := by omega
      dsimp [f]
      rw [hleft, hright, pow_succ S, pow_succ' U]
      noncomm_ring

/-! ## Split and unsplit Cayley steps -/

abbrev splitStepHat {n : ℕ} (A B : Mat n) (alpha : ℝ) :
    E n →L[ℂ] E n :=
  Chat A alpha * Chat B alpha

abbrev unsplitStepHat {n : ℕ} (A B : Mat n) (alpha : ℝ) :
    E n →L[ℂ] E n :=
  Chat (A + B) alpha

/-- The requested telescoping identity for the split and unsplit Cayley
steps. -/
theorem cayley_split_unsplit_telescoping {n : ℕ}
    (alpha : ℝ) (A B : Mat n) (N : ℕ) :
    splitStepHat A B alpha ^ N - unsplitStepHat A B alpha ^ N =
      ∑ k ∈ Finset.range N,
        splitStepHat A B alpha ^ (N - 1 - k) *
          (splitStepHat A B alpha - unsplitStepHat A B alpha) *
          unsplitStepHat A B alpha ^ k :=
  pow_sub_pow_telescoping (splitStepHat A B alpha)
    (unsplitStepHat A B alpha) N

/-! ## Unconditional unitary norm transport -/

theorem splitStepHat_mem_unitary {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    splitStepHat A B alpha ∈ unitary (E n →L[ℂ] E n) := by
  exact (unitary (E n →L[ℂ] E n)).mul_mem
    (unitary_toEuclideanCLM (cayley_unitary alpha A hA))
    (unitary_toEuclideanCLM (cayley_unitary alpha B hB))

theorem unsplitStepHat_mem_unitary {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    unsplitStepHat A B alpha ∈ unitary (E n →L[ℂ] E n) := by
  exact unitary_toEuclideanCLM
    (cayley_unitary alpha (A + B) (hA.add hB))

/-- Left and right multiplication by arbitrary powers of unitary operators
does not alter the middle operator norm. This formulation remains valid in
dimension zero, where an unconditional claim that the unitary norm equals one
would be false. -/
private theorem unitary_sandwich_norm {n : ℕ}
    {S U D : E n →L[ℂ] E n}
    (hS : S ∈ unitary (E n →L[ℂ] E n))
    (hU : U ∈ unitary (E n →L[ℂ] E n))
    (p q : ℕ) :
    ‖S ^ p * D * U ^ q‖ = ‖D‖ := by
  have hSp : S ^ p ∈ unitary (E n →L[ℂ] E n) :=
    (unitary (E n →L[ℂ] E n)).pow_mem hS p
  have hUq : U ^ q ∈ unitary (E n →L[ℂ] E n) :=
    (unitary (E n →L[ℂ] E n)).pow_mem hU q
  calc
    ‖S ^ p * D * U ^ q‖ = ‖S ^ p * D‖ :=
      CStarRing.norm_mul_mem_unitary (S ^ p * D) hUq
    _ = ‖D‖ := CStarRing.norm_mem_unitary_mul D hSp

/-- Lady Windermere's Fan estimate for two unitary continuous endomorphisms.
It is unconditional in the Euclidean dimension and includes `N = 0`. -/
theorem unitary_pow_sub_pow_opNorm_le {n : ℕ}
    (S U : E n →L[ℂ] E n) (N : ℕ)
    (hS : S ∈ unitary (E n →L[ℂ] E n))
    (hU : U ∈ unitary (E n →L[ℂ] E n)) :
    ‖S ^ N - U ^ N‖ ≤ (N : ℝ) * ‖S - U‖ := by
  rw [pow_sub_pow_telescoping S U N]
  calc
    ‖∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k‖ ≤
        ∑ k ∈ Finset.range N,
          ‖S ^ (N - 1 - k) * (S - U) * U ^ k‖ :=
      norm_sum_le _ _
    _ = ∑ _k ∈ Finset.range N, ‖S - U‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact unitary_sandwich_norm hS hU (N - 1 - k) k
    _ = (N : ℝ) * ‖S - U‖ := by simp

/-! ## Global finite-step error estimate -/

/-- The split-versus-unsplit Cayley error grows at most linearly in the finite
step count, with the exact Step-3 local coefficient. All norms are induced
operator norms on `E n →L[ℂ] E n`. -/
theorem cayley_split_unsplit_global_opNorm_le {n : ℕ}
    (alpha : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖splitStepHat A B alpha ^ N - unsplitStepHat A B alpha ^ N‖ ≤
      (N : ℝ) * 4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
  calc
    ‖splitStepHat A B alpha ^ N - unsplitStepHat A B alpha ^ N‖ ≤
        (N : ℝ) *
          ‖splitStepHat A B alpha - unsplitStepHat A B alpha‖ :=
      unitary_pow_sub_pow_opNorm_le
        (splitStepHat A B alpha) (unsplitStepHat A B alpha) N
        (splitStepHat_mem_unitary alpha A B hA hB)
        (unsplitStepHat_mem_unitary alpha A B hA hB)
    _ ≤ (N : ℝ) *
        (4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖) :=
      mul_le_mul_of_nonneg_left
        (cayley_split_unsplit_defect_opNorm_le alpha A B hA hB)
        (by positivity)
    _ = (N : ℝ) * 4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
      ring

end NDEAEvolve.Exp003

#check @NDEAEvolve.Exp003.pow_sub_pow_telescoping
#check @NDEAEvolve.Exp003.cayley_split_unsplit_telescoping
#check @NDEAEvolve.Exp003.unitary_pow_sub_pow_opNorm_le
#check @NDEAEvolve.Exp003.cayley_split_unsplit_global_opNorm_le
#print axioms NDEAEvolve.Exp003.pow_sub_pow_telescoping
#print axioms NDEAEvolve.Exp003.cayley_split_unsplit_telescoping
#print axioms NDEAEvolve.Exp003.unitary_pow_sub_pow_opNorm_le
#print axioms NDEAEvolve.Exp003.cayley_split_unsplit_global_opNorm_le
