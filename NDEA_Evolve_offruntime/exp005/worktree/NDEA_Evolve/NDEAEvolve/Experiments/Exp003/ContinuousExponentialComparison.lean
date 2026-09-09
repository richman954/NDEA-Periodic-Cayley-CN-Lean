import NDEAEvolve.Experiments.Exp003.FiniteNTelescopingGlobalBound
import NDEAEvolve.Experiments.Exp003.ExponentialRemainder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Cayley evolution compared with the continuous exponential

The sign and scale follow the existing convention `(1-iαH)(1+iαH)⁻¹`.
The local cubic bound has an explicit small-step hypothesis. All norms are
induced norms of continuous endomorphisms, including in dimension zero.
-/

noncomputable section
open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

local instance (n : ℕ) : NormedAlgebra ℚ (E n →L[ℂ] E n) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E n →L[ℂ] E n)

abbrev skewHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  (Complex.I * (alpha : ℂ)) • operatorOf H

abbrev exactStepHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  NormedSpace.exp ((-2 : ℂ) • skewHat H alpha)

theorem skewHat_norm {n : ℕ} (H : Mat n) (alpha : ℝ) :
    ‖skewHat H alpha‖ = |alpha| * ‖operatorOf H‖ := by
  simp [skewHat, norm_smul, Complex.norm_real, Real.norm_eq_abs]

private theorem quadratic_poly_scale {R : Type*} [Ring R] [Algebra ℂ R]
    (X : R) :
    1 + (-2 : ℂ) • X + (1 / 2 : ℂ) • ((-2 : ℂ) • X) ^ 2 =
      1 - X - X + X ^ 2 + X ^ 2 := by
  rw [smul_pow, smul_smul]
  norm_num
  module

private theorem cayley_quadratic_remainder_core {R : Type*} [Ring R]
    (X RX : R) (hRX : (1 + X) * RX = 1) :
    (1 - X) * RX - (1 - X - X + X ^ 2 + X ^ 2) =
      -(X ^ 3 * RX + X ^ 3 * RX) := by
  calc
    (1 - X) * RX - (1 - X - X + X ^ 2 + X ^ 2) =
        -(X ^ 3 * RX + X ^ 3 * RX) +
          (1 - X - X + X ^ 2 + X ^ 2) * ((1 + X) * RX - 1) := by
            noncomm_ring
    _ = -(X ^ 3 * RX + X ^ 3 * RX) := by rw [hRX]; simp

theorem cayley_quadratic_remainder {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    Chat H alpha -
        (1 - skewHat H alpha - skewHat H alpha +
          skewHat H alpha ^ 2 + skewHat H alpha ^ 2) =
      -(skewHat H alpha ^ 3 * Rhat H alpha +
        skewHat H alpha ^ 3 * Rhat H alpha) := by
  have hC : Chat H alpha = (1 - skewHat H alpha) * Rhat H alpha := by
    simp only [Chat, cayley, cayleyN, skewPart, cscalar, map_mul, map_sub,
      map_one, map_smul, skewHat, operatorOf, Rhat]
  have hR : (1 + skewHat H alpha) * Rhat H alpha = 1 := by
    simpa only [cayleyD, skewPart, cscalar, map_mul, map_add, map_one,
      map_smul, skewHat, operatorOf, Rhat] using
      congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
        (cayleyD_mul_cayleyR alpha H hH)
  rw [hC]
  exact cayley_quadratic_remainder_core _ _ hR

theorem cayley_quadratic_remainder_opNorm_le {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    ‖Chat H alpha -
        (1 - skewHat H alpha - skewHat H alpha +
          skewHat H alpha ^ 2 + skewHat H alpha ^ 2)‖ ≤
      2 * ‖skewHat H alpha‖ ^ 3 := by
  rw [cayley_quadratic_remainder alpha H hH, norm_neg]
  have hterm : ‖skewHat H alpha ^ 3 * Rhat H alpha‖ ≤
      ‖skewHat H alpha‖ ^ 3 := by
    calc
      _ ≤ ‖skewHat H alpha ^ 3‖ * ‖Rhat H alpha‖ := norm_mul_le _ _
      _ ≤ ‖skewHat H alpha‖ ^ 3 * 1 :=
        mul_le_mul (norm_pow_le' _ (by decide))
          (cayleyR_toEuclideanCLM_opNorm_le_one alpha H hH)
          (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ‖skewHat H alpha ^ 3 * Rhat H alpha‖ +
        ‖skewHat H alpha ^ 3 * Rhat H alpha‖ := norm_add_le _ _
    _ ≤ 2 * ‖skewHat H alpha‖ ^ 3 := by linarith

theorem exactStepHat_mem_unitary {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    exactStepHat H alpha ∈ unitary (E n →L[ℂ] E n) := by
  have hself : IsSelfAdjoint (operatorOf H) := by
    change star (operatorOf H) = operatorOf H
    simpa only [operatorOf, map_star] using
      congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
        (hermitian_star hH)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change (-2 : ℂ) • ((Complex.I * (alpha : ℂ)) • operatorOf H) ∈ _
  rw [smul_smul]
  apply hself.smul_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp

/-- Cubic one-step comparison with the correct continuous time scale. -/
theorem cayley_exp_local_opNorm_le {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian)
    (hstep : 4 * |alpha| * ‖operatorOf H‖ ≤ 1) :
    ‖Chat H alpha - exactStepHat H alpha‖ ≤
      18 * |alpha| ^ 3 * ‖operatorOf H‖ ^ 3 := by
  let X := skewHat H alpha
  let P : E n →L[ℂ] E n := 1 - X - X + X ^ 2 + X ^ 2
  have hnorm : ‖(-2 : ℂ) • X‖ = 2 * ‖X‖ := by
    rw [norm_smul]; norm_num
  have hsmall : ‖(-2 : ℂ) • X‖ ≤ 1 / 2 := by
    rw [hnorm]
    dsimp [X]
    rw [skewHat_norm]
    nlinarith
  have hpoly : 1 + (-2 : ℂ) • X +
      (1 / 2 : ℂ) • ((-2 : ℂ) • X) ^ 2 = P :=
    quadratic_poly_scale X
  have hexp := exp_quadratic_remainder_opNorm_le
    (show ‖(1 : E n →L[ℂ] E n)‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
    ((-2 : ℂ) • X) hsmall
  rw [hpoly, hnorm] at hexp
  have hc : ‖Chat H alpha - P‖ ≤ 2 * ‖X‖ ^ 3 :=
    cayley_quadratic_remainder_opNorm_le alpha H hH
  have htri : ‖Chat H alpha - exactStepHat H alpha‖ ≤
      ‖Chat H alpha - P‖ + ‖exactStepHat H alpha - P‖ := by
    calc
      _ ≤ ‖Chat H alpha - P‖ + ‖P - exactStepHat H alpha‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev P (exactStepHat H alpha)]
  calc
    _ ≤ 18 * ‖X‖ ^ 3 := by dsimp [exactStepHat] at htri ⊢; nlinarith
    _ = _ := by dsimp [X]; rw [skewHat_norm]; ring

/-- The unsplit discrete error against the N-fold exact exponential. -/
theorem cayley_exp_global_opNorm_le {n : ℕ}
    (alpha : ℝ) (H : Mat n) (N : ℕ) (hH : H.IsHermitian)
    (hstep : 4 * |alpha| * ‖operatorOf H‖ ≤ 1) :
    ‖Chat H alpha ^ N - exactStepHat H alpha ^ N‖ ≤
      (N : ℝ) * 18 * |alpha| ^ 3 * ‖operatorOf H‖ ^ 3 := by
  calc
    _ ≤ (N : ℝ) * ‖Chat H alpha - exactStepHat H alpha‖ :=
      unitary_pow_sub_pow_opNorm_le _ _ N
        (unitary_toEuclideanCLM (cayley_unitary alpha H hH))
        (exactStepHat_mem_unitary alpha H hH)
    _ ≤ (N : ℝ) * (18 * |alpha| ^ 3 * ‖operatorOf H‖ ^ 3) :=
      mul_le_mul_of_nonneg_left (cayley_exp_local_opNorm_le alpha H hH hstep)
        (by positivity)
    _ = _ := by ring

theorem split_cayley_exp_global_opNorm_le {n : ℕ}
    (alpha : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hstep : 4 * |alpha| * ‖operatorOf (A + B)‖ ≤ 1) :
    ‖splitStepHat A B alpha ^ N - exactStepHat (A + B) alpha ^ N‖ ≤
      (N : ℝ) * 4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ +
        (N : ℝ) * 18 * |alpha| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 := by
  exact (norm_sub_le_norm_sub_add_norm_sub (splitStepHat A B alpha ^ N)
    (unsplitStepHat A B alpha ^ N) (exactStepHat (A + B) alpha ^ N)).trans
    (add_le_add (cayley_split_unsplit_global_opNorm_le alpha A B N hA hB)
      (cayley_exp_global_opNorm_le alpha (A + B) N (hA.add hB) hstep))

/-- N exact substeps cover physical time t. N must be positive. -/
theorem exactStepHat_fixed_time_pow {n : ℕ}
    (t : ℝ) (H : Mat n) (N : ℕ) (hN : 0 < N) :
    exactStepHat H (t / (2 * (N : ℝ))) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf H) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [exactStepHat, ← NormedSpace.exp_nsmul,
    ← Nat.cast_smul_eq_nsmul ℂ N, skewHat, smul_smul, smul_smul]
  congr 1
  congr 1
  push_cast
  field_simp [hNc]

/-- Explicit first-order splitting and second-order unsplit error at fixed
physical time. The small-step condition is eventually true for every t. -/
theorem split_cayley_fixed_time_error_le {n : ℕ}
    (t : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * |t| * ‖operatorOf (A + B)‖ ≤ (N : ℝ)) :
    ‖splitStepHat A B (t / (2 * (N : ℝ))) ^ N -
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖ ≤
      t ^ 2 / (N : ℝ) * ‖operatorOf A‖ * ‖operatorOf B‖ +
        (9 / 4 : ℝ) * |t| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have habs : |t / (2 * (N : ℝ))| = |t| / (2 * (N : ℝ)) := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hNr)]
  have hs : 4 * |t / (2 * (N : ℝ))| * ‖operatorOf (A + B)‖ ≤ 1 := by
    rw [habs]
    have hid : 4 * (|t| / (2 * (N : ℝ))) * ‖operatorOf (A + B)‖ =
        (2 * |t| * ‖operatorOf (A + B)‖) / (N : ℝ) := by ring
    rw [hid]
    exact (div_le_one hNr).2 hstep
  have hb := split_cayley_exp_global_opNorm_le
    (t / (2 * (N : ℝ))) A B N hA hB hs
  rw [exactStepHat_fixed_time_pow t (A + B) N hN, habs] at hb
  convert hb using 1 <;> field_simp [hNr.ne'] <;> ring

end NDEAEvolve.Exp003

#check @NDEAEvolve.Exp003.cayley_exp_local_opNorm_le
#check @NDEAEvolve.Exp003.split_cayley_fixed_time_error_le
#print axioms NDEAEvolve.Exp003.cayley_quadratic_remainder
#print axioms NDEAEvolve.Exp003.cayley_exp_local_opNorm_le
#print axioms NDEAEvolve.Exp003.exactStepHat_fixed_time_pow
#print axioms NDEAEvolve.Exp003.split_cayley_fixed_time_error_le
