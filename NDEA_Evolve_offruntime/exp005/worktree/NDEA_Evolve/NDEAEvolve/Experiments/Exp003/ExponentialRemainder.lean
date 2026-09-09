import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A cubic exponential remainder on a norm half-ball

The exponential is the Banach-algebra exponential. The explicit hypothesis
`‖1‖ ≤ 1` permits the trivial algebra, as required for zero-dimensional
continuous endomorphisms. The proof dominates the exponential series by a
geometric series; it uses no differentiability or spectral decomposition.
-/

noncomputable section

open scoped BigOperators

namespace NDEAEvolve.Exp003

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

private theorem norm_pow_le_with_norm_one_le (hOne : ‖(1 : 𝔸)‖ ≤ 1)
    (Z : 𝔸) (m : ℕ) : ‖Z ^ m‖ ≤ ‖Z‖ ^ m := by
  cases m with
  | zero => simpa using hOne
  | succ m => exact norm_pow_le' Z (Nat.succ_pos m)

/-- Explicit quadratic Taylor approximation for the Banach-algebra
exponential, valid including the trivial algebra. -/
theorem exp_quadratic_remainder_opNorm_le
    (hOne : ‖(1 : 𝔸)‖ ≤ 1) (Z : 𝔸) (hZ : ‖Z‖ ≤ 1 / 2) :
    ‖NormedSpace.exp Z - (1 + Z + (1 / 2 : ℂ) • Z ^ 2)‖ ≤
      2 * ‖Z‖ ^ 3 := by
  have hcoeff (m : ℕ) : ‖(m.factorial : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, RCLike.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hterm (m : ℕ) :
      ‖(m.factorial : ℂ)⁻¹ • Z ^ m‖ ≤ 1 * ‖Z‖ ^ m := by
    rw [norm_smul]
    exact mul_le_mul (hcoeff m) (norm_pow_le_with_norm_one_le hOne Z m)
      (norm_nonneg _) (by positivity)
  have htail := norm_sub_le_of_geometric_bound_of_hasSum
    (show ‖Z‖ < 1 by linarith) hterm
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z) 3
  have hsum :
      (∑ m ∈ Finset.range 3, (m.factorial : ℂ)⁻¹ • Z ^ m) =
        1 + Z + (1 / 2 : ℂ) • Z ^ 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum, norm_sub_rev, one_mul] at htail
  apply htail.trans
  apply (div_le_iff₀ (show 0 < 1 - ‖Z‖ by linarith)).2
  have hscaled := mul_le_mul_of_nonneg_left hZ
    (show 0 ≤ 2 * ‖Z‖ ^ 3 by positivity)
  nlinarith

end NDEAEvolve.Exp003

#check @NDEAEvolve.Exp003.exp_quadratic_remainder_opNorm_le
#print axioms NDEAEvolve.Exp003.exp_quadratic_remainder_opNorm_le
