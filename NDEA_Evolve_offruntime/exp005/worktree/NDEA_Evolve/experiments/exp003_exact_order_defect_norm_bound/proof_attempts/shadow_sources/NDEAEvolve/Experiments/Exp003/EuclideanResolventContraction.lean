/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/
import NDEAEvolve.Experiments.Exp002.OperatorCayley
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Euclidean resolvent contraction

This Step-1 module derives the Euclidean induced operator-norm estimate for the
inverse Cayley denominator from the exact affine Cayley identity and the norm
preservation already verified in Experiment 002.
-/

noncomputable section

open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

private theorem cayley_eq_two_cayleyR_sub_one {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayley α A = cayleyR α A + cayleyR α A - 1 := by
  have hRight : (1 + skewPart α A) * cayleyR α A = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR α A hA
  simpa only [cayley, cayleyN, two_mul] using
    cayley_affine_of_right_inverse
      (skewPart α A) (cayleyR α A) hRight

/-- The inverse Cayley denominator is the arithmetic average of identity and
    the Cayley factor. -/
theorem cayleyR_eq_average {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayleyR α A = (1 / 2 : ℂ) • (1 + cayley α A) := by
  rw [cayley_eq_two_cayleyR_sub_one α A hA]
  module

/-- The averaging identity transported to continuous linear maps on the
    standard finite-dimensional complex Euclidean space. -/
theorem cayleyR_toEuclideanCLM_eq_average {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) =
      (1 / 2 : ℂ) •
        (1 + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A)) := by
  simpa only [map_smul, map_add, map_one] using
    congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayleyR_eq_average α A hA)

/-- Pointwise resolvent nonexpansiveness in the standard complex Euclidean norm. -/
theorem cayleyR_toEuclideanCLM_apply_norm_le {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) x‖ ≤ ‖x‖ := by
  have havg := congrArg
    (fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => T x)
    (cayleyR_toEuclideanCLM_eq_average α A hA)
  have havg' :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) x =
        (1 / 2 : ℂ) •
          (x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x) := by
    simpa using havg
  rw [havg']
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ‖(1 / 2 : ℂ) •
        (x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x)‖
        = (1 / 2 : ℝ) *
            ‖x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x‖ := by
              rw [norm_smul, hhalf]
    _ ≤ (1 / 2 : ℝ) *
          (‖x‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖x‖ := by
      rw [cayley_preserves_norm α A hA x]
      ring

/-- The inverse Cayley denominator has induced Euclidean operator norm at most
    one for every dimension and every real parameter. -/
theorem cayleyR_toEuclideanCLM_opNorm_le_one {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A)‖ ≤ 1 := by
  refine (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A)).opNorm_le_bound
    zero_le_one ?_
  intro x
  simpa only [one_mul] using cayleyR_toEuclideanCLM_apply_norm_le α A hA x

namespace AdversarialWitnesses

abbrev Mat1 := Mat 1

/-- Zero step is admitted, independently of the zero-generator example. -/
theorem alpha_zero_opNorm_le_one :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 0 (1 : Mat1))‖ ≤ 1 :=
  cayleyR_toEuclideanCLM_opNorm_le_one 0 (1 : Mat1) Matrix.isHermitian_one

/-- A zero generator is admitted at a nonzero step. -/
theorem zero_generator_opNorm_le_one :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 (0 : Mat1))‖ ≤ 1 :=
  cayleyR_toEuclideanCLM_opNorm_le_one 1 (0 : Mat1) Matrix.isHermitian_zero

/-- Negative real steps are admitted; no positivity premise is needed. -/
theorem negative_alpha_opNorm_le_one :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR (-1) (1 : Mat1))‖ ≤ 1 :=
  cayleyR_toEuclideanCLM_opNorm_le_one (-1) (1 : Mat1) Matrix.isHermitian_one

/-- At `A = 0` the resolvent is identity. -/
theorem zero_generator_cayleyR_eq_one :
    cayleyR 1 (0 : Mat1) = 1 := by
  simp [cayleyR, cayleyD, skewPart, cscalar]

theorem zero_generator_opNorm_eq_one :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 (0 : Mat1))‖ = 1 := by
  rw [zero_generator_cayleyR_eq_one]
  simp

/-- Hence the universal non-strict estimate cannot be strengthened to `< 1`. -/
theorem zero_generator_not_strict_contraction :
    ¬ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 (0 : Mat1))‖ < 1 := by
  rw [zero_generator_opNorm_eq_one]
  exact lt_irrefl 1

/-- The scalar matrix `i/2`; it is deliberately non-Hermitian. -/
def imaginaryHalf : Mat1 := (Complex.I / 2) • (1 : Mat1)

def twoIdentity : Mat1 := (2 : ℂ) • (1 : Mat1)

theorem imaginaryHalf_not_hermitian : ¬ imaginaryHalf.IsHermitian := by
  intro h
  have h00 := h.apply (0 : Fin 1) (0 : Fin 1)
  have him := congrArg Complex.im h00
  norm_num [imaginaryHalf] at him

/-- For this non-Hermitian generator, `I + iA = (1/2)I` and its inverse is `2I`. -/
theorem imaginaryHalf_cayleyR_eq_twoIdentity :
    cayleyR 1 imaginaryHalf = twoIdentity := by
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cayleyD, skewPart, cscalar, imaginaryHalf, twoIdentity,
    Matrix.mul_apply, Fin.sum_univ_one, smul_smul, Complex.I_mul_I]
  <;> rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]
  <;> norm_num

theorem imaginaryHalf_resolvent_opNorm_eq_two :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 imaginaryHalf)‖ = 2 := by
  rw [imaginaryHalf_cayleyR_eq_twoIdentity]
  unfold twoIdentity
  rw [map_smul, map_one, norm_smul, norm_one]
  norm_num

/-- Dropping Hermiticity permits an expansive resolvent. -/
theorem nonhermitian_resolvent_not_nonexpansive :
    ¬ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 imaginaryHalf)‖ ≤ 1 := by
  rw [imaginaryHalf_resolvent_opNorm_eq_two]
  norm_num

end AdversarialWitnesses

end NDEAEvolve.Exp003

/- Exact public signatures and transitive dependency output are emitted during
   the qualifying build and cryptographically bound in the evidence bundle. -/
#check ("NDEA_EXP003_AUDIT_BEGIN" : String)
#check @NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average
#check @NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le
#check @NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one
#print NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average
#print NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le
#print NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one
#print axioms NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_eq_average
#print axioms NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_apply_norm_le
#print axioms NDEAEvolve.Exp003.cayleyR_toEuclideanCLM_opNorm_le_one
#check ("NDEA_EXP003_AUDIT_END" : String)

#check @NDEAEvolve.Exp003.AdversarialWitnesses.alpha_zero_opNorm_le_one
#check @NDEAEvolve.Exp003.AdversarialWitnesses.zero_generator_opNorm_le_one
#check @NDEAEvolve.Exp003.AdversarialWitnesses.negative_alpha_opNorm_le_one
#check @NDEAEvolve.Exp003.AdversarialWitnesses.zero_generator_not_strict_contraction
#check @NDEAEvolve.Exp003.AdversarialWitnesses.nonhermitian_resolvent_not_nonexpansive
