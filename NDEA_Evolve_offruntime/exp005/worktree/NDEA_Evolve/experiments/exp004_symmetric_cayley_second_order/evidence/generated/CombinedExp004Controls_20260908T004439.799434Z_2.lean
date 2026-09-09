import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean SHA256 0849ce5520b2582112b733d681b7901a64cf45d82a37a53605194c6147e2a15f
/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/

/-!
# Finite noncommutative Cayley composition

The public hypotheses use `Matrix.IsHermitian`. All products are ordered exactly as
written; no pairwise commutativity assumption is made for the composition theorem.
-/

noncomputable section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace NDEAEvolve
namespace Exp002

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cscalar (α : ℝ) : ℂ := Complex.I * (α : ℂ)

def skewPart {n : ℕ} (α : ℝ) (A : Mat n) : Mat n := cscalar α • A

def cayleyD {n : ℕ} (α : ℝ) (A : Mat n) : Mat n := 1 + skewPart α A

def cayleyN {n : ℕ} (α : ℝ) (A : Mat n) : Mat n := 1 - skewPart α A

def cayleyR {n : ℕ} (α : ℝ) (A : Mat n) : Mat n := (cayleyD α A)⁻¹

def cayley {n : ℕ} (α : ℝ) (A : Mat n) : Mat n := cayleyN α A * cayleyR α A

def IsUnitary {n : ℕ} (U : Mat n) : Prop :=
  U * star U = 1 ∧ star U * U = 1

def commutator {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X

theorem star_cscalar (α : ℝ) : star (cscalar α) = -cscalar α := by
  apply Complex.ext <;> simp [cscalar]

theorem hermitian_star {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : star A = A := by
  rw [Matrix.star_eq_conjTranspose]
  exact hA.eq

theorem skewPart_star {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    star (skewPart α A) = -skewPart α A := by
  simp [skewPart, star_smul, star_cscalar, hermitian_star hA]

theorem cayleyD_star {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    star (cayleyD α A) = cayleyN α A := by
  simp [cayleyD, cayleyN, skewPart_star α A hA, sub_eq_add_neg]

theorem cayleyD_normal {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayleyD α A * star (cayleyD α A) =
      star (cayleyD α A) * cayleyD α A := by
  rw [cayleyD_star α A hA]
  unfold cayleyD cayleyN
  noncomm_ring

theorem cayleyD_gram_eq {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    star (cayleyD α A) * cayleyD α A =
      1 + star (skewPart α A) * skewPart α A := by
  rw [cayleyD_star α A hA]
  change (1 - skewPart α A) * (1 + skewPart α A) =
    1 + star (skewPart α A) * skewPart α A
  rw [skewPart_star α A hA]
  noncomm_ring

theorem cayleyD_gram_posDef {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    Matrix.PosDef (star (cayleyD α A) * cayleyD α A) := by
  rw [cayleyD_gram_eq α A hA]
  have hOne : Matrix.PosDef (1 : Mat n) := Matrix.PosDef.one
  have hGram : Matrix.PosSemidef (star (skewPart α A) * skewPart α A) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.posSemidef_conjTranspose_mul_self (skewPart α A))
  exact hOne.add_posSemidef hGram

/-- Hermiticity and a real parameter imply denominator invertibility. -/
theorem cayleyD_isUnit {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    IsUnit (cayleyD α A) := by
  have hGramUnit : IsUnit (star (cayleyD α A) * cayleyD α A) :=
    (cayleyD_gram_posDef α A hA).isUnit
  have hGramInjective :
      Function.Injective (star (cayleyD α A) * cayleyD α A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hGramUnit
  have hDInjective : Function.Injective (cayleyD α A).mulVec := by
    intro x y hxy
    apply hGramInjective
    simpa only [Matrix.mulVec_mulVec] using
      congrArg (fun z => (star (cayleyD α A)).mulVec z) hxy
  exact Matrix.mulVec_injective_iff_isUnit.mp hDInjective

theorem cayleyD_det_isUnit {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    IsUnit (cayleyD α A).det :=
  (Matrix.isUnit_iff_isUnit_det (cayleyD α A)).mp (cayleyD_isUnit α A hA)

theorem cayleyD_det_ne_zero {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    (cayleyD α A).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (cayleyD_det_isUnit α A hA)

theorem cayleyD_mul_cayleyR {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayleyD α A * cayleyR α A = 1 := by
  exact Matrix.mul_nonsing_inv (cayleyD α A) (cayleyD_det_isUnit α A hA)

theorem cayleyR_mul_cayleyD {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayleyR α A * cayleyD α A = 1 := by
  exact Matrix.nonsing_inv_mul (cayleyD α A) (cayleyD_det_isUnit α A hA)

/-- Reconstructed clean star-ring core; no generated result is trusted. -/
theorem unitary_of_normal_and_inverse {R : Type*} [Ring R] [StarRing R]
    (D Rinv : R)
    (hNormal : D * star D = star D * D)
    (hRight : D * Rinv = 1)
    (hLeft : Rinv * D = 1) :
    (star D * Rinv) * star (star D * Rinv) = 1 ∧
      star (star D * Rinv) * (star D * Rinv) = 1 := by
  have hComm : Rinv * star D = star D * Rinv := by
    calc
      Rinv * star D = Rinv * star D * 1 := by rw [mul_one]
      _ = Rinv * star D * (D * Rinv) := by rw [← hRight]
      _ = Rinv * (star D * D) * Rinv := by simp only [mul_assoc]
      _ = Rinv * (D * star D) * Rinv := by rw [← hNormal]
      _ = (Rinv * D) * star D * Rinv := by simp only [← mul_assoc]
      _ = star D * Rinv := by rw [hLeft, one_mul]
  constructor
  · calc
      (star D * Rinv) * star (star D * Rinv)
          = (star D * Rinv) * (star Rinv * D) := by rw [star_mul, star_star]
      _ = (Rinv * star D) * star Rinv * D := by rw [hComm]; simp only [mul_assoc]
      _ = Rinv * star (Rinv * D) * D := by rw [star_mul]; simp only [mul_assoc]
      _ = Rinv * star 1 * D := by rw [hLeft]
      _ = Rinv * D := by rw [star_one, mul_one]
      _ = 1 := hLeft
  · calc
      star (star D * Rinv) * (star D * Rinv)
          = (star Rinv * D) * (star D * Rinv) := by rw [star_mul, star_star]
      _ = star Rinv * (D * star D) * Rinv := by simp only [mul_assoc]
      _ = star Rinv * (star D * D) * Rinv := by rw [hNormal]
      _ = star (D * Rinv) * (D * Rinv) := by rw [star_mul]; simp only [mul_assoc]
      _ = 1 * 1 := by rw [hRight, star_one]
      _ = 1 := one_mul 1

/-- A finite Hermitian Cayley factor is two-sided unitary. -/
theorem cayley_unitary {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    IsUnitary (cayley α A) := by
  unfold cayley IsUnitary
  rw [← cayleyD_star α A hA]
  exact unitary_of_normal_and_inverse
    (cayleyD α A) (cayleyR α A)
    (cayleyD_normal α A hA)
    (cayleyD_mul_cayleyR α A hA)
    (cayleyR_mul_cayleyD α A hA)

theorem isUnitary_one {n : ℕ} : IsUnitary (1 : Mat n) := by
  simp [IsUnitary]

theorem isUnitary_mul {n : ℕ} {U V : Mat n}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  rcases hU with ⟨hUr, hUl⟩
  rcases hV with ⟨hVr, hVl⟩
  constructor
  · rw [star_mul]
    calc
      U * V * (star V * star U) = U * (V * star V) * star U := by noncomm_ring
      _ = U * star U := by rw [hVr]; simp
      _ = 1 := hUr
  · rw [star_mul]
    calc
      (star V * star U) * (U * V) = star V * (star U * U) * V := by noncomm_ring
      _ = star V * V := by rw [hUl]; simp
      _ = 1 := hVl

/-- Chronological list convention: the head acts first. -/
def orderedProduct {n : ℕ} : List (Mat n) → Mat n
  | [] => 1
  | U :: Us => orderedProduct Us * U

theorem orderedProduct_cons {n : ℕ} (U : Mat n) (Us : List (Mat n)) :
    orderedProduct (U :: Us) = orderedProduct Us * U := rfl

theorem orderedProduct_cons_mulVec {n : ℕ} (U : Mat n) (Us : List (Mat n))
    (x : Fin n → ℂ) :
    (orderedProduct (U :: Us)).mulVec x =
      (orderedProduct Us).mulVec (U.mulVec x) := by
  symm
  exact Matrix.mulVec_mulVec x (orderedProduct Us) U

theorem orderedProduct_unitary {n : ℕ} (Us : List (Mat n))
    (hUs : ∀ U ∈ Us, IsUnitary U) : IsUnitary (orderedProduct Us) := by
  induction Us with
  | nil => exact isUnitary_one
  | cons U Us ih =>
      apply isUnitary_mul
      · exact ih (fun V hV => hUs V (by simp [hV]))
      · exact hUs U (by simp)

structure CayleyStep (n : ℕ) where
  α : ℝ
  generator : Mat n

def CayleyStep.factor {n : ℕ} (step : CayleyStep n) : Mat n :=
  cayley step.α step.generator

def orderedCayleyProduct {n : ℕ} (steps : List (CayleyStep n)) : Mat n :=
  orderedProduct (steps.map CayleyStep.factor)

/-- Variable real steps and changing Hermitian generators; no commutativity premise. -/
theorem orderedCayleyProduct_unitary {n : ℕ} (steps : List (CayleyStep n))
    (hHermitian : ∀ step ∈ steps, step.generator.IsHermitian) :
    IsUnitary (orderedCayleyProduct steps) := by
  apply orderedProduct_unitary
  intro U hU
  rcases List.mem_map.mp hU with ⟨step, hStep, rfl⟩
  exact cayley_unitary step.α step.generator (hHermitian step hStep)

theorem unitary_toEuclideanCLM {n : ℕ} {U : Mat n} (hU : IsUnitary U) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) U ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
  rw [Unitary.mem_iff]
  constructor
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M) hU.2
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M) hU.1

theorem unitary_preserves_inner {n : ℕ} {U : Mat n} (hU : IsUnitary U)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) U x)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) U y) = inner ℂ x y :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (unitary_toEuclideanCLM hU) x y

theorem unitary_preserves_norm {n : ℕ} {U : Mat n} (hU : IsUnitary U)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) U x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (unitary_toEuclideanCLM hU) x

theorem cayley_preserves_inner {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) y) = inner ℂ x y :=
  unitary_preserves_inner (cayley_unitary α A hA) x y

theorem cayley_preserves_norm {n : ℕ} (α : ℝ) (A : Mat n) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x‖ = ‖x‖ :=
  unitary_preserves_norm (cayley_unitary α A hA) x

theorem orderedCayleyProduct_preserves_inner {n : ℕ} (steps : List (CayleyStep n))
    (hHermitian : ∀ step ∈ steps, step.generator.IsHermitian)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (orderedCayleyProduct steps) x)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (orderedCayleyProduct steps) y) = inner ℂ x y :=
  unitary_preserves_inner (orderedCayleyProduct_unitary steps hHermitian) x y

/-- Headline variable-step norm preservation in the standard Euclidean norm. -/
theorem orderedCayleyProduct_preserves_norm {n : ℕ} (steps : List (CayleyStep n))
    (hHermitian : ∀ step ∈ steps, step.generator.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (orderedCayleyProduct steps) x‖ = ‖x‖ :=
  unitary_preserves_norm (orderedCayleyProduct_unitary steps hHermitian) x

/-! ## Pure noncommutative order-defect algebra -/

theorem inverse_commutator_factorization {R₀ : Type*} [Ring R₀]
    (D E RD RE : R₀)
    (hDR : D * RD = 1) (hRD : RD * D = 1)
    (hER : E * RE = 1) (hRE : RE * E = 1) :
    commutator RD RE = RD * RE * commutator D E * RE * RD := by
  have hTerm₁ : RD * RE * D * E * RE * RD = RD * RE := by
    calc
      RD * RE * D * E * RE * RD = RD * RE * D * (E * RE) * RD := by noncomm_ring
      _ = RD * RE := by rw [hER]; simp [mul_assoc, hDR]
  have hTerm₂ : RD * RE * E * D * RE * RD = RE * RD := by
    calc
      RD * RE * E * D * RE * RD = RD * (RE * E) * D * RE * RD := by noncomm_ring
      _ = RE * RD := by rw [hRE]; simp [hRD]
  unfold commutator
  rw [show RD * RE * (D * E - E * D) * RE * RD =
      RD * RE * D * E * RE * RD - RD * RE * E * D * RE * RD by noncomm_ring]
  rw [hTerm₁, hTerm₂]

theorem cayley_affine_of_right_inverse {R₀ : Type*} [Ring R₀] (X RX : R₀)
    (hRight : (1 + X) * RX = 1) :
    (1 - X) * RX = (2 : R₀) * RX - 1 := by
  calc
    (1 - X) * RX = (2 - (1 + X)) * RX := by noncomm_ring
    _ = (2 : R₀) * RX - (1 + X) * RX := by noncomm_ring
    _ = (2 : R₀) * RX - 1 := by rw [hRight]

theorem cayley_commutator_core {R₀ : Type*} [Ring R₀]
    (X Y RX RY : R₀)
    (hDXR : (1 + X) * RX = 1) (hRXD : RX * (1 + X) = 1)
    (hDYR : (1 + Y) * RY = 1) (hRYD : RY * (1 + Y) = 1) :
    commutator ((1 - X) * RX) ((1 - Y) * RY) =
      (4 : R₀) * (RX * RY * commutator X Y * RY * RX) := by
  rw [cayley_affine_of_right_inverse X RX hDXR,
      cayley_affine_of_right_inverse Y RY hDYR]
  have hInverse := inverse_commutator_factorization
    (1 + X) (1 + Y) RX RY hDXR hRXD hDYR hRYD
  have hDenom : commutator (1 + X) (1 + Y) = commutator X Y := by
    unfold commutator
    noncomm_ring
  rw [hDenom] at hInverse
  calc
    commutator ((2 : R₀) * RX - 1) ((2 : R₀) * RY - 1) =
        (4 : R₀) * commutator RX RY := by unfold commutator; noncomm_ring
    _ = (4 : R₀) * (RX * RY * commutator X Y * RY * RX) := by rw [hInverse]

theorem skewPart_commutator {n : ℕ} (α β : ℝ) (A B : Mat n) :
    commutator (skewPart α A) (skewPart β B) =
      (-((α : ℂ) * (β : ℂ))) • commutator A B := by
  unfold commutator skewPart cscalar
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
  simp only [smul_smul]
  have hαβ : Complex.I * (α : ℂ) * (Complex.I * (β : ℂ)) =
      -((α : ℂ) * (β : ℂ)) := by
    calc
      Complex.I * (α : ℂ) * (Complex.I * (β : ℂ)) =
          (Complex.I * Complex.I) * ((α : ℂ) * (β : ℂ)) := by ring
      _ = -((α : ℂ) * (β : ℂ)) := by rw [Complex.I_mul_I]; simp
  have hβα : Complex.I * (β : ℂ) * (Complex.I * (α : ℂ)) =
      -((α : ℂ) * (β : ℂ)) := by
    calc
      Complex.I * (β : ℂ) * (Complex.I * (α : ℂ)) =
          (Complex.I * Complex.I) * ((α : ℂ) * (β : ℂ)) := by ring
      _ = -((α : ℂ) * (β : ℂ)) := by rw [Complex.I_mul_I]; simp
  rw [hαβ, hβα, smul_sub]

theorem matrix_four_mul {n : ℕ} (Z : Mat n) :
    (4 : Mat n) * Z = (4 : ℂ) • Z := by
  calc
    (4 : Mat n) * Z = 4 • Z := (nsmul_eq_mul 4 Z).symm
    _ = (4 : ℂ) • Z := (Nat.cast_smul_eq_nsmul ℂ 4 Z).symm

/-- Exact frozen order-defect identity; Hermiticity is not required here. -/
theorem cayley_order_defect {n : ℕ} (α β : ℝ) (A B : Mat n)
    (hDαR : cayleyD α A * cayleyR α A = 1)
    (hRαD : cayleyR α A * cayleyD α A = 1)
    (hDβR : cayleyD β B * cayleyR β B = 1)
    (hRβD : cayleyR β B * cayleyD β B = 1) :
    commutator (cayley α A) (cayley β B) =
      (-4 * (α : ℂ) * (β : ℂ)) •
        (cayleyR α A * cayleyR β B * commutator A B *
          cayleyR β B * cayleyR α A) := by
  have hCore := cayley_commutator_core
    (skewPart α A) (skewPart β B) (cayleyR α A) (cayleyR β B)
    hDαR hRαD hDβR hRβD
  change commutator (cayleyN α A * cayleyR α A)
      (cayleyN β B * cayleyR β B) = _
  change commutator ((1 - skewPart α A) * cayleyR α A)
      ((1 - skewPart β B) * cayleyR β B) = _
  rw [hCore, skewPart_commutator]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [matrix_four_mul, smul_smul]
  congr 1
  ring

theorem inverse_sandwich_eq_zero_iff {R₀ : Type*} [Ring R₀]
    (D E RD RE K : R₀)
    (hDR : D * RD = 1) (hRD : RD * D = 1)
    (hER : E * RE = 1) (hRE : RE * E = 1) :
    RD * RE * K * RE * RD = 0 ↔ K = 0 := by
  constructor
  · intro h
    have hCancel : E * D * (RD * RE * K * RE * RD) * D * E = K := by
      calc
        E * D * (RD * RE * K * RE * RD) * D * E =
            E * (D * RD) * RE * K * RE * (RD * D) * E := by noncomm_ring
        _ = E * RE * K * RE * E := by rw [hDR, hRD]; simp
        _ = K * RE * E := by rw [hER]; simp
        _ = K := by rw [mul_assoc, hRE, mul_one]
    calc
      K = E * D * (RD * RE * K * RE * RD) * D * E := hCancel.symm
      _ = 0 := by rw [h]; simp
  · intro h
    rw [h]
    simp

theorem commutator_eq_zero_iff_commute {R₀ : Type*} [Ring R₀] (X Y : R₀) :
    commutator X Y = 0 ↔ Commute X Y := by
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h.eq

/-- Nonzero real steps make Cayley commutation equivalent to generator commutation. -/
theorem cayley_commute_iff_of_inverse_laws {n : ℕ} (α β : ℝ) (A B : Mat n)
    (hDαR : cayleyD α A * cayleyR α A = 1)
    (hRαD : cayleyR α A * cayleyD α A = 1)
    (hDβR : cayleyD β B * cayleyR β B = 1)
    (hRβD : cayleyR β B * cayleyD β B = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    Commute (cayley α A) (cayley β B) ↔ Commute A B := by
  rw [← commutator_eq_zero_iff_commute, ← commutator_eq_zero_iff_commute]
  rw [cayley_order_defect α β A B hDαR hRαD hDβR hRβD]
  have hScalar : (-4 * (α : ℂ) * (β : ℂ)) ≠ 0 := by
    norm_num [hα, hβ]
  rw [smul_eq_zero]
  simp only [hScalar, false_or]
  exact inverse_sandwich_eq_zero_iff
    (cayleyD α A) (cayleyD β B) (cayleyR α A) (cayleyR β B) (commutator A B)
    hDαR hRαD hDβR hRβD

/-- Hermitian headline corollary: denominator assumptions are derived, not assumed. -/
theorem hermitian_cayley_commute_iff {n : ℕ} (α β : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hαβ : α * β ≠ 0) :
    Commute (cayley α A) (cayley β B) ↔ Commute A B := by
  have hα : α ≠ 0 := left_ne_zero_of_mul hαβ
  have hβ : β ≠ 0 := right_ne_zero_of_mul hαβ
  exact cayley_commute_iff_of_inverse_laws α β A B
    (cayleyD_mul_cayleyR α A hA) (cayleyR_mul_cayleyD α A hA)
    (cayleyD_mul_cayleyR β B hB) (cayleyR_mul_cayleyD β B hB)
    hα hβ

end Exp002
end NDEAEvolve
-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean SHA256 419451c84966173a2db4020c7f8fcb29d4e6bce6dbcc77640fcc6e09835fbe05
/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean SHA256 216a8625424d696ff5c5716d8fd2712ec6041dca54442de9e5bcef31a895024d

noncomputable section
open NDEAEvolve.Exp002
namespace NDEAEvolve.Exp003

abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Rhat {n : ℕ} (X : Mat n) (γ : ℝ) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR γ X)
abbrev Chat {n : ℕ} (X : Mat n) (γ : ℝ) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley γ X)
abbrev operatorOf {n : ℕ} (X : Mat n) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) X

private theorem cayley_order_defect_CLM {n : ℕ}
    (α β : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Chat A α * Chat B β - Chat B β * Chat A α =
      (-4 * (α : ℂ) * (β : ℂ)) •
        (Rhat A α * Rhat B β *
          (operatorOf A * operatorOf B - operatorOf B * operatorOf A) *
          Rhat B β * Rhat A α) := by
  simpa only [NDEAEvolve.Exp002.commutator, map_mul, map_sub, map_smul] using
    congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayley_order_defect α β A B
        (cayleyD_mul_cayleyR α A hA) (cayleyR_mul_cayleyD α A hA)
        (cayleyD_mul_cayleyR β B hB) (cayleyR_mul_cayleyD β B hB))

/-- The exact order-defect bound in the induced Euclidean operator norm. -/
theorem cayley_order_defect_opNorm_le {n : ℕ}
    (α β : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Chat A α * Chat B β - Chat B β * Chat A α‖ ≤
      4 * |α * β| *
        ‖operatorOf A * operatorOf B - operatorOf B * operatorOf A‖ := by
  let K := operatorOf A * operatorOf B - operatorOf B * operatorOf A
  rw [cayley_order_defect_CLM α β A B hA hB, norm_smul]
  have hs : ‖(-4 * (α : ℂ) * (β : ℂ))‖ = 4 * |α * β| := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_mul]
    ring
  rw [hs]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (abs_nonneg _))
  have hRα : ‖Rhat A α‖ ≤ 1 := cayleyR_toEuclideanCLM_opNorm_le_one α A hA
  have hRβ : ‖Rhat B β‖ ≤ 1 := cayleyR_toEuclideanCLM_opNorm_le_one β B hB
  change ‖Rhat A α * Rhat B β * K * Rhat B β * Rhat A α‖ ≤ ‖K‖
  calc
    ‖Rhat A α * Rhat B β * K * Rhat B β * Rhat A α‖
        ≤ ‖Rhat A α * Rhat B β * K * Rhat B β‖ * ‖Rhat A α‖ := norm_mul_le _ _
    _ ≤ ‖Rhat A α * Rhat B β * K * Rhat B β‖ := by
      simpa using mul_le_mul_of_nonneg_left hRα (norm_nonneg _)
    _ ≤ ‖Rhat A α * Rhat B β * K‖ * ‖Rhat B β‖ := norm_mul_le _ _
    _ ≤ ‖Rhat A α * Rhat B β * K‖ := by
      simpa using mul_le_mul_of_nonneg_left hRβ (norm_nonneg _)
    _ ≤ ‖Rhat A α * Rhat B β‖ * ‖K‖ := norm_mul_le _ _
    _ ≤ (‖Rhat A α‖ * ‖Rhat B β‖) * ‖K‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * 1) * ‖K‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hRα hRβ (norm_nonneg _) zero_le_one) (norm_nonneg _)
    _ = ‖K‖ := by ring

end NDEAEvolve.Exp003

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean SHA256 be1cfe32010bebc8b87b0982480a33d61f4d5ada9ccb19aa03a668699954e8b5

/-!
# Exact split-versus-unsplit Cayley defect

This Step-3 module proves the exact local defect identity for two Cayley
factors and its induced Euclidean operator-norm estimate.  The proof is
purely finite-dimensional and algebraic; the only analytic input is the
Step-1 resolvent contraction theorem.
-/

noncomputable section

open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

/-! ## Pure noncommutative algebra -/

/-- Ring-theoretic core of the split-versus-unsplit defect.  The three
denominators are represented only through the inverse laws used by the
calculation. -/
theorem cayley_split_defect_core {R₀ : Type*} [Ring R₀]
    (X Y RX RY RXY : R₀)
    (hXR : (1 + X) * RX = 1)
    (hYR : (1 + Y) * RY = 1)
    (hXYR : (1 + (X + Y)) * RXY = 1)
    (hRXY : RXY * (1 + (X + Y)) = 1) :
    ((1 - X) * RX) * ((1 - Y) * RY) - (1 - (X + Y)) * RXY =
      (2 : R₀) *
        (X * RX * Y * RY - RXY * Y * X * RX * RY) := by
  have hXRX : X * RX = 1 - RX := by
    calc
      X * RX = (1 + X) * RX - RX := by noncomm_ring
      _ = 1 - RX := by rw [hXR]
  have hYRY : Y * RY = 1 - RY := by
    calc
      Y * RY = (1 + Y) * RY - RY := by noncomm_ring
      _ = 1 - RY := by rw [hYR]
  have hQuadratic :
      X * RX * Y * RY = 1 - RX - RY + RX * RY := by
    calc
      X * RX * Y * RY = (X * RX) * (Y * RY) := by noncomm_ring
      _ = (1 - RX) * (1 - RY) := by rw [hXRX, hYRY]
      _ = 1 - RX - RY + RX * RY := by noncomm_ring
  have hDenominatorExpansion :
      (1 + (X + Y)) * RX * RY + Y * X * RX * RY = 1 := by
    calc
      (1 + (X + Y)) * RX * RY + Y * X * RX * RY =
          ((1 + X) * RX) * RY + Y * ((1 + X) * RX) * RY := by
            noncomm_ring
      _ = RY + Y * RY := by rw [hXR]; simp
      _ = (1 + Y) * RY := by noncomm_ring
      _ = 1 := hYR
  have hYX :
      Y * X * RX * RY = 1 - (1 + (X + Y)) * RX * RY := by
    calc
      Y * X * RX * RY =
          ((1 + (X + Y)) * RX * RY + Y * X * RX * RY) -
            (1 + (X + Y)) * RX * RY := by
              noncomm_ring
      _ = 1 - (1 + (X + Y)) * RX * RY := by
        rw [hDenominatorExpansion]
  have hResolventQuadratic :
      RXY * Y * X * RX * RY = RXY - RX * RY := by
    calc
      RXY * Y * X * RX * RY = RXY * (Y * X * RX * RY) := by
        noncomm_ring
      _ = RXY * (1 - (1 + (X + Y)) * RX * RY) := by rw [hYX]
      _ = RXY - (RXY * (1 + (X + Y))) * RX * RY := by
        noncomm_ring
      _ = RXY - RX * RY := by rw [hRXY]; simp
  rw [cayley_affine_of_right_inverse X RX hXR,
    cayley_affine_of_right_inverse Y RY hYR,
    cayley_affine_of_right_inverse (X + Y) RXY hXYR]
  rw [hQuadratic, hResolventQuadratic]
  noncomm_ring

private theorem matrix_two_mul {n : ℕ} (Z : Mat n) :
    (2 : Mat n) * Z = (2 : ℂ) • Z := by
  calc
    (2 : Mat n) * Z = 2 • Z := (nsmul_eq_mul 2 Z).symm
    _ = (2 : ℂ) • Z := (Nat.cast_smul_eq_nsmul ℂ 2 Z).symm

private theorem skewPart_split_quadratic {n : ℕ}
    (X Y RX RY RXY : Mat n) (alpha : ℝ) :
    skewPart alpha X * RX * skewPart alpha Y * RY -
        RXY * skewPart alpha Y * skewPart alpha X * RX * RY =
      ((alpha : ℂ) ^ 2) •
        (RXY * Y * X * RX * RY - X * RX * Y * RY) := by
  have hcscalar_sq :
      (Complex.I * (alpha : ℂ)) * (Complex.I * (alpha : ℂ)) =
        -((alpha : ℂ) ^ 2) := by
    calc
      (Complex.I * (alpha : ℂ)) * (Complex.I * (alpha : ℂ)) =
          (Complex.I * Complex.I) * ((alpha : ℂ) * (alpha : ℂ)) := by
            ring
      _ = -((alpha : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
  have hFirst :
      skewPart alpha X * RX * skewPart alpha Y * RY =
        (-((alpha : ℂ) ^ 2)) • (X * RX * Y * RY) := by
    simp only [skewPart, cscalar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcscalar_sq]
  have hSecond :
      RXY * skewPart alpha Y * skewPart alpha X * RX * RY =
        (-((alpha : ℂ) ^ 2)) • (RXY * Y * X * RX * RY) := by
    simp only [skewPart, cscalar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcscalar_sq]
  rw [hFirst, hSecond]
  module

/-! ## Exact matrix identity -/

/-- Exact split-versus-unsplit Cayley defect for arbitrary finite Hermitian
complex matrices and every real step, including zero and negative steps. -/
theorem cayley_split_unsplit_defect {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cayley alpha A * cayley alpha B - cayley alpha (A + B) =
      (2 * (alpha : ℂ) ^ 2) •
        (cayleyR alpha (A + B) * B * A * cayleyR alpha A * cayleyR alpha B -
          A * cayleyR alpha A * B * cayleyR alpha B) := by
  have hAB : (A + B).IsHermitian := hA.add hB
  have hSkewAdd :
      skewPart alpha (A + B) = skewPart alpha A + skewPart alpha B := by
    simp only [skewPart, smul_add]
  have hDAR :
      (1 + skewPart alpha A) * cayleyR alpha A = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha A hA
  have hDBR :
      (1 + skewPart alpha B) * cayleyR alpha B = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha B hB
  have hDABR :
      (1 + (skewPart alpha A + skewPart alpha B)) *
          cayleyR alpha (A + B) = 1 := by
    rw [← hSkewAdd]
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha (A + B) hAB
  have hRABD :
      cayleyR alpha (A + B) *
          (1 + (skewPart alpha A + skewPart alpha B)) = 1 := by
    rw [← hSkewAdd]
    simpa only [cayleyD] using cayleyR_mul_cayleyD alpha (A + B) hAB
  change
    ((1 - skewPart alpha A) * cayleyR alpha A) *
          ((1 - skewPart alpha B) * cayleyR alpha B) -
        (1 - skewPart alpha (A + B)) * cayleyR alpha (A + B) = _
  rw [hSkewAdd]
  calc
    ((1 - skewPart alpha A) * cayleyR alpha A) *
          ((1 - skewPart alpha B) * cayleyR alpha B) -
        (1 - (skewPart alpha A + skewPart alpha B)) *
          cayleyR alpha (A + B) =
        (2 : Mat n) *
          (skewPart alpha A * cayleyR alpha A *
                skewPart alpha B * cayleyR alpha B -
            cayleyR alpha (A + B) * skewPart alpha B *
              skewPart alpha A * cayleyR alpha A * cayleyR alpha B) :=
      cayley_split_defect_core
        (skewPart alpha A) (skewPart alpha B)
        (cayleyR alpha A) (cayleyR alpha B) (cayleyR alpha (A + B))
        hDAR hDBR hDABR hRABD
    _ = (2 * (alpha : ℂ) ^ 2) •
        (cayleyR alpha (A + B) * B * A * cayleyR alpha A *
              cayleyR alpha B -
          A * cayleyR alpha A * B * cayleyR alpha B) := by
      rw [skewPart_split_quadratic, matrix_two_mul, smul_smul]

/-! ## Continuous-linear-map transport and induced operator norm -/

private theorem cayley_split_unsplit_defect_CLM {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Chat A alpha * Chat B alpha - Chat (A + B) alpha =
      (2 * (alpha : ℂ) ^ 2) •
        (Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
              Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha) := by
  simpa only [map_mul, map_sub, map_smul] using
    congrArg
      (fun M : Mat n =>
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayley_split_unsplit_defect alpha A B hA hB)

/-- The exact local splitting defect is quadratically bounded in the real
step in the induced operator norm on the standard complex Euclidean space. -/
theorem cayley_split_unsplit_defect_opNorm_le {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Chat A alpha * Chat B alpha - Chat (A + B) alpha‖ ≤
      4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
  have hAB : (A + B).IsHermitian := hA.add hB
  have hRA : ‖Rhat A alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha A hA
  have hRB : ‖Rhat B alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha B hB
  have hRAB : ‖Rhat (A + B) alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha (A + B) hAB
  have hFirst :
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
          Rhat B alpha‖ ≤ ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
          Rhat B alpha‖ ≤
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha‖ *
            ‖Rhat B alpha‖ := norm_mul_le _ _
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A *
            Rhat A alpha‖ := by
        simpa using mul_le_mul_of_nonneg_left hRB (norm_nonneg _)
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A‖ *
            ‖Rhat A alpha‖ := norm_mul_le _ _
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A‖ := by
        simpa using mul_le_mul_of_nonneg_left hRA (norm_nonneg _)
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B‖ * ‖operatorOf A‖ :=
        norm_mul_le _ _
      _ ≤ (‖Rhat (A + B) alpha‖ * ‖operatorOf B‖) *
            ‖operatorOf A‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * ‖operatorOf B‖) * ‖operatorOf A‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hRAB (norm_nonneg _)) (norm_nonneg _)
      _ = ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  have hSecond :
      ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
          ‖operatorOf A * Rhat A alpha * operatorOf B‖ *
            ‖Rhat B alpha‖ := norm_mul_le _ _
      _ ≤ ‖operatorOf A * Rhat A alpha * operatorOf B‖ := by
        simpa using mul_le_mul_of_nonneg_left hRB (norm_nonneg _)
      _ ≤ ‖operatorOf A * Rhat A alpha‖ * ‖operatorOf B‖ :=
        norm_mul_le _ _
      _ ≤ (‖operatorOf A‖ * ‖Rhat A alpha‖) * ‖operatorOf B‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖operatorOf A‖ * 1) * ‖operatorOf B‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRA (norm_nonneg _)) (norm_nonneg _)
      _ = ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  have hInside :
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
            Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
            Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
              Rhat B alpha‖ +
            ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ :=
        norm_sub_le _ _
      _ ≤ ‖operatorOf A‖ * ‖operatorOf B‖ +
            ‖operatorOf A‖ * ‖operatorOf B‖ := add_le_add hFirst hSecond
      _ = 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  rw [cayley_split_unsplit_defect_CLM alpha A B hA hB, norm_smul]
  have hScalar :
      ‖(2 : ℂ) * (alpha : ℂ) ^ 2‖ = 2 * alpha ^ 2 := by
    simp only [norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hScalar]
  calc
    2 * alpha ^ 2 *
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
                Rhat B alpha -
            operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        2 * alpha ^ 2 * (2 * ‖operatorOf A‖ * ‖operatorOf B‖) :=
      mul_le_mul_of_nonneg_left hInside
        (mul_nonneg (by norm_num) (sq_nonneg alpha))
    _ = 4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by ring

end NDEAEvolve.Exp003

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean SHA256 afd2134c867b75a648f159aad3a321f11fe2e352d98d24a6574c4da9e3a70aea

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExponentialRemainder.lean SHA256 6d56da15466b7c6920916a72a0eb66daf209442ecf3d3170468eb78ad323b747

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExponentialRemainder.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialComparison.lean SHA256 e7ec9be08d19d315d6c0cffab4f74ec47d650c1a1344cae3469e9596c84cdb85

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialComparison.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialLimit.lean SHA256 f009e79daa8f4728743fa8d6ca6f879dc990a66ab2d9ab5535d9186120bde333

/-!
# Operator-norm convergence of split Cayley evolution

The finite-step comparison is applied only after the step count exceeds its
explicit threshold. This yields convergence for every real time and every
finite Euclidean dimension, including dimension zero.
-/

noncomputable section

open Filter
open scoped Topology
open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

/-- The explicit first- and second-order fixed-time error majorant vanishes
as the natural step count tends to infinity. -/
theorem split_cayley_fixed_time_majorant_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n) :
    Tendsto
      (fun N : ℕ =>
        t ^ 2 / (N : ℝ) * ‖operatorOf A‖ * ‖operatorOf B‖ +
          (9 / 4 : ℝ) * |t| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 /
            (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hfirst : Tendsto
      (fun N : ℕ => t ^ 2 / (N : ℝ) * ‖operatorOf A‖ * ‖operatorOf B‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_const_div_atTop_nhds_zero_nat (t ^ 2)).mul_const
        ‖operatorOf A‖).mul_const ‖operatorOf B‖
  have hsecond : Tendsto
      (fun N : ℕ =>
        (9 / 4 : ℝ) * |t| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 /
          (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds
        (x := (9 / 4 : ℝ) * |t| ^ 3 * ‖operatorOf (A + B)‖ ^ 3)).mul
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
  simpa only [zero_add] using hfirst.add hsecond

/-- The split Cayley approximation minus the continuous exponential tends
to zero in the induced operator-norm topology. -/
theorem split_cayley_fixed_time_difference_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        splitStepHat A B (t / (2 * (N : ℝ))) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (split_cayley_fixed_time_majorant_tendsto_zero t A B)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * |t| * ‖operatorOf (A + B)‖)] with N hN hstep
  exact split_cayley_fixed_time_error_le t A B N hA hB hN hstep

/-- At each fixed real time, the split Cayley powers converge to the
exponential generated by the sum of the two Hermitian operators. -/
theorem split_cayley_fixed_time_tendsto_exp {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun N : ℕ => splitStepHat A B (t / (2 * (N : ℝ))) ^ N)
      atTop
      (𝓝 (NormedSpace.exp
        ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))) := by
  exact tendsto_sub_nhds_zero_iff.mp
    (split_cayley_fixed_time_difference_tendsto_zero t A B hA hB)

/-- The numerical value of the induced operator-norm error tends to zero. -/
theorem split_cayley_fixed_time_error_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        ‖splitStepHat A B (t / (2 * (N : ℝ))) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (split_cayley_fixed_time_difference_tendsto_zero t A B hA hB).norm

end NDEAEvolve.Exp003

-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialLimit.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyLocal.lean SHA256 776ddc1a68ed1e4acf8e2c587916ed45240542d7fa93fd5106a49685bde9d8e3

/-!
# Cubic local consistency of the symmetric Cayley composition

The three factors approximate exp(-i h A/2), exp(-i h B), exp(-i h A/2),
respectively: their Cayley parameters are h/4, h/2, h/4.
The ordered quadratic terms cancel without a commutativity hypothesis.
Every analytic estimate uses the induced continuous-endomorphism norm.
-/

noncomputable section

open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004

abbrev symmetricStepHat {n : ℕ} (A B : Mat n) (h : ℝ) : E n →L[ℂ] E n :=
  Chat A (h / 4) * Chat B (h / 2) * Chat A (h / 4)

private def linPart {R : Type*} [Ring R] (X : R) : R := -(X + X)
private def quadPart {R : Type*} [Ring R] (X : R) : R := X ^ 2 + X ^ 2
private def cayleyPoly {R : Type*} [Ring R] (X : R) : R :=
  1 + linPart X + quadPart X

private theorem cayleyPoly_eq {R : Type*} [Ring R] (X : R) :
    cayleyPoly X = 1 - X - X + X ^ 2 + X ^ 2 := by
  unfold cayleyPoly linPart quadPart
  noncomm_ring

/-- All degree-zero, degree-one, and degree-two terms agree. The four
displayed groups on the right have degree at least three. -/
private theorem symmetric_quadratic_cancellation {R : Type*} [Ring R]
    (X Y : R) :
    cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly (X + X + Y) =
      (linPart X * quadPart Y + quadPart X * linPart Y +
        quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * linPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * quadPart X := by
  unfold cayleyPoly linPart quadPart
  noncomm_ring

private theorem norm_mul_bound {R : Type*} [NormedRing R]
    {X Y : R} {x y : ℝ} (hX : ‖X‖ ≤ x) (hY : ‖Y‖ ≤ y) :
    ‖X * Y‖ ≤ x * y :=
  (norm_mul_le X Y).trans
    (mul_le_mul hX hY (norm_nonneg Y) ((norm_nonneg X).trans hX))

private theorem linPart_norm_le {R : Type*} [NormedRing R]
    {X : R} {r : ℝ} (hX : ‖X‖ ≤ r) : ‖linPart X‖ ≤ 2 * r := by
  unfold linPart
  rw [norm_neg]
  exact (norm_add_le X X).trans (by linarith)

private theorem quadPart_norm_le {R : Type*} [NormedRing R]
    {X : R} {r : ℝ} (_hr : 0 ≤ r) (hX : ‖X‖ ≤ r) :
    ‖quadPart X‖ ≤ 2 * r ^ 2 := by
  have hp : ‖X ^ 2‖ ≤ r ^ 2 := by
    calc
      _ ≤ ‖X‖ ^ 2 := norm_pow_le' X (by decide)
      _ ≤ r ^ 2 := by gcongr
  unfold quadPart
  exact (norm_add_le (X ^ 2) (X ^ 2)).trans (by linarith)

private theorem cayleyPoly_norm_le_five {R : Type*} [NormedRing R]
    (hOne : ‖(1 : R)‖ ≤ 1) {X : R} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hX : ‖X‖ ≤ r) :
    ‖cayleyPoly X‖ ≤ 5 := by
  have hl := linPart_norm_le hX
  have hq := quadPart_norm_le hr hX
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  unfold cayleyPoly
  calc
    ‖1 + linPart X + quadPart X‖ ≤ ‖1 + linPart X‖ + ‖quadPart X‖ :=
      norm_add_le _ _
    _ ≤ (‖(1 : R)‖ + ‖linPart X‖) + ‖quadPart X‖ :=
      add_le_add (norm_add_le (1 : R) (linPart X)) (le_refl ‖quadPart X‖)
    _ ≤ 5 := by linarith

/-- A norm estimate for the explicitly ordered polynomial remainder. -/
private theorem symmetric_quadratic_remainder_norm_le {R : Type*} [NormedRing R]
    (hOne : ‖(1 : R)‖ ≤ 1) {X Y : R} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r) :
    ‖cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly (X + X + Y)‖ ≤
      100 * r ^ 3 := by
  have hlX := linPart_norm_le hX
  have hlY := linPart_norm_le hY
  have hqX := quadPart_norm_le hr hX
  have hqY := quadPart_norm_le hr hY
  have hPX := cayleyPoly_norm_le_five hOne hr hr1 hX
  have hr4 : r ^ 4 ≤ r ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ r ^ 3 by positivity)
    nlinarith
  have hpair : ‖linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y‖ ≤ 12 * r ^ 3 := by
    have h1 := norm_mul_bound hlX hqY
    have h2 := norm_mul_bound hqX hlY
    have h3 := norm_mul_bound hqX hqY
    have ha := norm_add_le (linPart X * quadPart Y) (quadPart X * linPart Y)
    have hb := norm_add_le (linPart X * quadPart Y + quadPart X * linPart Y)
      (quadPart X * quadPart Y)
    nlinarith
  have hlin : ‖linPart X + linPart Y‖ ≤ 4 * r :=
    (norm_add_le _ _).trans (by linarith)
  have hquad : ‖quadPart X + linPart X * linPart Y + quadPart Y‖ ≤ 8 * r ^ 2 := by
    have hm := norm_mul_bound hlX hlY
    have ha := norm_add_le (quadPart X) (linPart X * linPart Y)
    have hb := norm_add_le (quadPart X + linPart X * linPart Y) (quadPart Y)
    nlinarith
  have h1 := norm_mul_bound hpair hPX
  have h2 := norm_mul_bound hlin hqX
  have h3 := norm_mul_bound hquad hlX
  have h4 := norm_mul_bound hquad hqX
  rw [symmetric_quadratic_cancellation]
  have ha := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X)
    ((linPart X + linPart Y) * quadPart X)
  have hb := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X)
    ((quadPart X + linPart X * linPart Y + quadPart Y) * linPart X)
  have hc := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * linPart X)
    ((quadPart X + linPart X * linPart Y + quadPart Y) * quadPart X)
  nlinarith

private theorem sandwich_replacement_norm_le {R : Type*} [NormedRing R]
    {S T P Q : R} {d : ℝ}
    (hS : ‖S‖ ≤ 1) (hT : ‖T‖ ≤ 1)
    (hP : ‖P‖ ≤ 5) (hQ : ‖Q‖ ≤ 5)
    (hSP : ‖S - P‖ ≤ d) (hTQ : ‖T - Q‖ ≤ d) :
    ‖S * T * S - P * Q * P‖ ≤ 31 * d := by
  have hid : S * T * S - P * Q * P =
      (S - P) * T * S + P * (T - Q) * S + P * Q * (S - P) := by
    noncomm_ring
  have h1 := norm_mul_bound (norm_mul_bound hSP hT) hS
  have h2 := norm_mul_bound (norm_mul_bound hP hTQ) hS
  have h3 := norm_mul_bound (norm_mul_bound hP hQ) hSP
  rw [hid]
  have ha := norm_add_le ((S - P) * T * S) (P * (T - Q) * S)
  have hb := norm_add_le ((S - P) * T * S + P * (T - Q) * S) (P * Q * (S - P))
  nlinarith

private theorem cayley_norm_le_one {n : ℕ}
    (a : ℝ) (H : Mat n) (hH : H.IsHermitian) : ‖Chat H a‖ ≤ 1 := by
  have hu := unitary_toEuclideanCLM (cayley_unitary a H hH)
  calc
    ‖Chat H a‖ = ‖(1 : E n →L[ℂ] E n)‖ := by
      simpa only [mul_one] using
        CStarRing.norm_mem_unitary_mul (1 : E n →L[ℂ] E n) hu
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

/-- The sum generator is the sum of the three ordered substep generators. -/
private theorem symmetric_skew_sum {n : ℕ} (h : ℝ) (A B : Mat n) :
    skewHat A (h / 4) + skewHat A (h / 4) + skewHat B (h / 2) =
      skewHat (A + B) (h / 2) := by
  simp only [skewHat, operatorOf, map_add, smul_add]
  push_cast
  module

/-- A cubic local error bound for symmetric Cayley splitting, for arbitrary
finite Hermitian generators, including dimension zero and either time sign. -/
theorem symmetric_cayley_exp_local_opNorm_le {n : ℕ}
    (h : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hstep : 2 * |h| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1) :
    ‖symmetricStepHat A B h - exactStepHat (A + B) (h / 2)‖ ≤
      1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 := by
  let r : ℝ := |h| * (‖operatorOf A‖ + ‖operatorOf B‖)
  let X := skewHat A (h / 4)
  let Y := skewHat B (h / 2)
  let W := skewHat (A + B) (h / 2)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by dsimp [r]; nlinarith [hstep]
  have hr1 : r ≤ 1 := by linarith
  have hsum : ‖operatorOf (A + B)‖ ≤ ‖operatorOf A‖ + ‖operatorOf B‖ := by
    simpa only [operatorOf, map_add] using norm_add_le (operatorOf A) (operatorOf B)
  have hpa : |h| * ‖operatorOf A‖ ≤ r := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (abs_nonneg h)
  have hpb : |h| * ‖operatorOf B‖ ≤ r := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (abs_nonneg h)
  have hpw : |h| * ‖operatorOf (A + B)‖ ≤ r :=
    mul_le_mul_of_nonneg_left hsum (abs_nonneg h)
  have hX : ‖X‖ ≤ r := by
    change ‖skewHat A (h / 4)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (4 : ℝ) by norm_num)]
    nlinarith only [hpa, hr]
  have hY : ‖Y‖ ≤ r := by
    change ‖skewHat B (h / 2)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpb, hr]
  have hW : ‖W‖ ≤ r := by
    change ‖skewHat (A + B) (h / 2)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpw, hr]
  have hOne : ‖(1 : E n →L[ℂ] E n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hPX := cayleyPoly_norm_le_five hOne hr hr1 hX
  have hPY := cayleyPoly_norm_le_five hOne hr hr1 hY
  have hCX : ‖Chat A (h / 4) - cayleyPoly X‖ ≤ 2 * r ^ 3 := by
    rw [cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖X‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 4) A hA
      _ ≤ 2 * r ^ 3 := by gcongr
  have hCY : ‖Chat B (h / 2) - cayleyPoly Y‖ ≤ 2 * r ^ 3 := by
    rw [cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖Y‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 2) B hB
      _ ≤ 2 * r ^ 3 := by gcongr
  have hreplace : ‖symmetricStepHat A B h - cayleyPoly X * cayleyPoly Y * cayleyPoly X‖ ≤
      62 * r ^ 3 := by
    have hb := sandwich_replacement_norm_le
      (cayley_norm_le_one (h / 4) A hA) (cayley_norm_le_one (h / 2) B hB)
      hPX hPY hCX hCY
    change ‖symmetricStepHat A B h - cayleyPoly X * cayleyPoly Y * cayleyPoly X‖ ≤
      31 * (2 * r ^ 3) at hb
    nlinarith
  have hcancel : ‖cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly W‖ ≤
      100 * r ^ 3 := by
    have hb := symmetric_quadratic_remainder_norm_le hOne hr hr1 hX hY
    have hid : X + X + Y = W := symmetric_skew_sum h A B
    rwa [hid] at hb
  have hCW : ‖cayleyPoly W - Chat (A + B) (h / 2)‖ ≤ 2 * r ^ 3 := by
    rw [norm_sub_rev, cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖W‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 2) (A + B) (hA.add hB)
      _ ≤ 2 * r ^ 3 := by gcongr
  have hs : 4 * |h / 2| * ‖operatorOf (A + B)‖ ≤ 1 := by
    rw [abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpw, hrhalf]
  have hCE : ‖Chat (A + B) (h / 2) - exactStepHat (A + B) (h / 2)‖ ≤
      18 * r ^ 3 := by
    calc
      _ ≤ 18 * |h / 2| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 :=
        cayley_exp_local_opNorm_le (h / 2) (A + B) (hA.add hB) hs
      _ = 18 * ‖W‖ ^ 3 := by change _ = 18 * ‖skewHat (A + B) (h / 2)‖ ^ 3; rw [skewHat_norm]; ring
      _ ≤ 18 * r ^ 3 := by gcongr
  have htri1 := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat A B h) (cayleyPoly X * cayleyPoly Y * cayleyPoly X)
    (exactStepHat (A + B) (h / 2))
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    (cayleyPoly X * cayleyPoly Y * cayleyPoly X) (cayleyPoly W)
    (exactStepHat (A + B) (h / 2))
  have htri3 := norm_sub_le_norm_sub_add_norm_sub
    (cayleyPoly W) (Chat (A + B) (h / 2)) (exactStepHat (A + B) (h / 2))
  calc
    _ ≤ 182 * r ^ 3 := by linarith
    _ ≤ 1000 * r ^ 3 := by nlinarith [pow_nonneg hr 3]
    _ = _ := by dsimp [r]; ring

end NDEAEvolve.Exp004

#check @NDEAEvolve.Exp004.symmetric_cayley_exp_local_opNorm_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_local_opNorm_le
-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyLocal.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyGlobal.lean SHA256 f4a02fabef86b256f8d4b31f9be657aebeb8f263c2b52d4c2afa53c314a65060

/-!
# Second-order global error for symmetric Cayley splitting

The finite-step estimate uses the already verified unitary telescoping fan.
At fixed physical time the cubic local error becomes an explicit inverse-square
step-count bound. Every norm is the induced continuous-linear-map norm.
-/

noncomputable section

open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004

/-- The symmetric Cayley step is unitary for every real step and every finite
dimension; there is no small-step or nonzero-dimension assumption. -/
theorem symmetricStepHat_mem_unitary {n : ℕ}
    (h : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    symmetricStepHat A B h ∈ unitary (E n →L[ℂ] E n) := by
  exact (unitary (E n →L[ℂ] E n)).mul_mem
    ((unitary (E n →L[ℂ] E n)).mul_mem
      (unitary_toEuclideanCLM (cayley_unitary (h / 4) A hA))
      (unitary_toEuclideanCLM (cayley_unitary (h / 2) B hB)))
    (unitary_toEuclideanCLM (cayley_unitary (h / 4) A hA))

/-- The finite telescoping identity, also valid for N=0. -/
theorem symmetric_cayley_exp_telescoping {n : ℕ}
    (h : ℝ) (A B : Mat n) (N : ℕ) :
    symmetricStepHat A B h ^ N - exactStepHat (A + B) (h / 2) ^ N =
      ∑ k ∈ Finset.range N,
        symmetricStepHat A B h ^ (N - 1 - k) *
          (symmetricStepHat A B h - exactStepHat (A + B) (h / 2)) *
          exactStepHat (A + B) (h / 2) ^ k :=
  pow_sub_pow_telescoping _ _ N

/-- Cubic local error accumulates at most linearly in the natural step count.
This all-N statement includes N=0 without a division convention. -/
theorem symmetric_cayley_exp_global_opNorm_le {n : ℕ}
    (h : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hstep : 2 * |h| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1) :
    ‖symmetricStepHat A B h ^ N - exactStepHat (A + B) (h / 2) ^ N‖ ≤
      (N : ℝ) * 1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 := by
  calc
    _ ≤ (N : ℝ) *
        ‖symmetricStepHat A B h - exactStepHat (A + B) (h / 2)‖ :=
      unitary_pow_sub_pow_opNorm_le _ _ N
        (symmetricStepHat_mem_unitary h A B hA hB)
        (exactStepHat_mem_unitary (h / 2) (A + B) (hA.add hB))
    _ ≤ (N : ℝ) *
        (1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (symmetric_cayley_exp_local_opNorm_le h A B hA hB hstep)
        (by positivity)
    _ = _ := by ring

/-- Explicit second-order global bound at fixed real physical time. The step
condition is eventually satisfied for every fixed time and pair of generators. -/
theorem symmetric_cayley_fixed_time_error_le {n : ℕ}
    (t : ℝ) (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ (N : ℝ)) :
    ‖symmetricStepHat A B (t / (N : ℝ)) ^ N -
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖ ≤
      1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have habs : |t / (N : ℝ)| = |t| / (N : ℝ) := by
    rw [abs_div, abs_of_pos hNr]
  have hs : 2 * |t / (N : ℝ)| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1 := by
    rw [habs]
    have hid : 2 * (|t| / (N : ℝ)) * (‖operatorOf A‖ + ‖operatorOf B‖) =
        (2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖)) / (N : ℝ) := by ring
    rw [hid]
    exact (div_le_one hNr).2 hstep
  have hb := symmetric_cayley_exp_global_opNorm_le
    (t / (N : ℝ)) A B N hA hB hs
  have hscale : t / (N : ℝ) / 2 = t / (2 * (N : ℝ)) := by ring
  rw [hscale, exactStepHat_fixed_time_pow t (A + B) N hN, habs] at hb
  convert hb using 1 <;> field_simp [hNr.ne'] <;> ring

/-- The explicit inverse-square majorant tends to zero. -/
theorem symmetric_cayley_fixed_time_majorant_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n) :
    Tendsto
      (fun N : ℕ =>
        1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds
      (x := 1000 * |t| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3)).mul
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)

/-- Operator-valued convergence of the error, including dimension zero. -/
theorem symmetric_cayley_fixed_time_difference_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        symmetricStepHat A B (t / (N : ℝ)) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (symmetric_cayley_fixed_time_majorant_tendsto_zero t A B)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * |t| * (‖operatorOf A‖ + ‖operatorOf B‖))] with N hN hstep
  exact symmetric_cayley_fixed_time_error_le t A B N hA hB hN hstep

/-- Symmetric Cayley powers converge to the exponential of the sum at each
fixed real time, without a step restriction on the convergence statement. -/
theorem symmetric_cayley_fixed_time_tendsto_exp {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun N : ℕ => symmetricStepHat A B (t / (N : ℝ)) ^ N)
      atTop
      (𝓝 (NormedSpace.exp
        ((-Complex.I * (t : ℂ)) • operatorOf (A + B)))) := by
  exact tendsto_sub_nhds_zero_iff.mp
    (symmetric_cayley_fixed_time_difference_tendsto_zero t A B hA hB)

/-- The induced operator-norm error tends to zero. -/
theorem symmetric_cayley_fixed_time_error_tendsto_zero {n : ℕ}
    (t : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Tendsto
      (fun N : ℕ =>
        ‖symmetricStepHat A B (t / (N : ℝ)) ^ N -
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B))‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (symmetric_cayley_fixed_time_difference_tendsto_zero t A B hA hB).norm

end NDEAEvolve.Exp004

#check @NDEAEvolve.Exp004.symmetric_cayley_exp_global_opNorm_le
#check @NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_le
#check @NDEAEvolve.Exp004.symmetric_cayley_fixed_time_tendsto_exp
#print axioms NDEAEvolve.Exp004.symmetricStepHat_mem_unitary
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_telescoping
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_global_opNorm_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_majorant_tendsto_zero
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_difference_tendsto_zero
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_tendsto_exp
#print axioms NDEAEvolve.Exp004.symmetric_cayley_fixed_time_error_tendsto_zero
-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyGlobal.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp004_symmetric_cayley_second_order/controls/lean/NegativeControls.lean SHA256 ec418e29f664fbe0d5fcb785256344b65c1cca9f2105a4fd792376e5b3928f6f

/-!
# Experiment 004 focused mathematical controls

Endpoint controls instantiate the actual operator scheme. Exact scalar
witnesses detect changes to its three-factor composition and parameter scale;
their coefficients are connected to the production continuous linear map.
The Pauli witness separately detects the quadratic commutator term that a
nonsymmetric composition leaves behind. Scalar witnesses alone would not
demonstrate that noncommutative quadratic defect.

Scalar Cayley calculations and Pauli definitions follow the corresponding
Experiment 002 and Experiment 003 controls, repeated in a separate namespace
without changing or importing the predecessor controls files.
-/

noncomputable section

open Filter Matrix
open scoped Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004.Controls

/-- Every finite count is exact at zero physical time, including N=0. -/
theorem zero_time_exact {n : ℕ} (A B : Mat n) (N : ℕ) :
    symmetricStepHat A B ((0 : ℝ) / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) := by
  have hz : ((-Complex.I * (0 : ℂ)) • operatorOf (A + B)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp
  rw [hz, NormedSpace.exp_zero]
  simp [symmetricStepHat, Chat, cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

/-- Zero powers agree independently of the positive-count fixed-time theorem. -/
theorem zero_power_identity {n : ℕ} (A B : Mat n) (h : ℝ) :
    symmetricStepHat A B h ^ 0 = (1 : E n →L[ℂ] E n) ∧
      exactStepHat (A + B) (h / 2) ^ 0 = (1 : E n →L[ℂ] E n) := by
  simp

/-- Zero generators remain exact for arbitrary real time and count. -/
theorem zero_generators_exact (n : ℕ) (t : ℝ) (N : ℕ) :
    symmetricStepHat (0 : Mat n) 0 (t / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) := by
  have hz : ((-Complex.I * (t : ℂ)) • operatorOf (0 : Mat n)) =
      (0 : E n →L[ℂ] E n) := by
    ext x
    simp [operatorOf]
  rw [hz, NormedSpace.exp_zero]
  simp [symmetricStepHat, Chat, operatorOf, cayley, cayleyN, cayleyR, cayleyD,
    skewPart, cscalar]

/-- The theorem retains dimension zero without assuming norm(identity)=1. -/
theorem zero_dimension_exact (A B : Mat 0) (t : ℝ) (N : ℕ) :
    symmetricStepHat A B (t / (N : ℝ)) ^ N =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf (A + B)) := by
  exact Subsingleton.elim _ _

/-- Negative physical time satisfies the same nonnegative cubic majorant. -/
theorem negative_time_bound {n : ℕ} (A B : Mat n) (N : ℕ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hN : 0 < N)
    (hstep : 2 * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ (N : ℝ)) :
    ‖symmetricStepHat A B ((-1 : ℝ) / (N : ℝ)) ^ N -
        NormedSpace.exp
          ((-Complex.I * ((-1 : ℝ) : ℂ)) • operatorOf (A + B))‖ ≤
      1000 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 / (N : ℝ) ^ 2 := by
  simpa using symmetric_cayley_fixed_time_error_le (-1) A B N hA hB hN
    (by simpa using hstep)

def scalarCayley (alpha : ℝ) : ℂ :=
  (1 - Complex.I * (alpha : ℂ)) / (1 + Complex.I * (alpha : ℂ))

private theorem scalar_denominator_ne_zero (alpha : ℝ) :
    (1 + Complex.I * (alpha : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem scalarCayley_matrix_entry (alpha : ℝ) :
    cayley alpha (1 : Mat 1) 0 0 = scalarCayley alpha := by
  simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar,
    Matrix.mul_apply, Matrix.inv_subsingleton, Ring.inverse_eq_inv,
    scalarCayley, div_eq_mul_inv]

theorem scalarCayley_one : scalarCayley 1 = -Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero 1)).2
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

theorem scalarCayley_half :
    scalarCayley (1 / 2) = ((3 : ℂ) - 4 * Complex.I) / 5 := by
  unfold scalarCayley
  apply (div_eq_iff (scalar_denominator_ne_zero (1 / 2))).2
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

def scalarSymmetric (h : ℝ) : ℂ :=
  scalarCayley (h / 4) * scalarCayley (h / 2) * scalarCayley (h / 4)

def scalarNonsymmetric (h : ℝ) : ℂ :=
  scalarCayley (h / 2) * scalarCayley (h / 2)

def scalarWrongQuarterStep (h : ℝ) : ℂ :=
  scalarCayley (h / 2) * scalarCayley (h / 2) * scalarCayley (h / 2)

def scalarSymmetricMatrix (h : ℝ) : Mat 1 :=
  cayley (h / 4) 1 * cayley (h / 2) 1 * cayley (h / 4) 1

theorem scalarSymmetric_matrix_entry (h : ℝ) :
    scalarSymmetricMatrix h 0 0 = scalarSymmetric h := by
  simp [scalarSymmetricMatrix, scalarSymmetric, Matrix.mul_apply,
    scalarCayley_matrix_entry]

/-- The production operator is the image of the stated ordered matrix
composition, including the mixed zero/unit generator example below. -/
theorem symmetricStepHat_matrix_bridge {n : ℕ} (A B : Mat n) (h : ℝ) :
    symmetricStepHat A B h =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
        (cayley (h / 4) A * cayley (h / 2) B * cayley (h / 4) A) := by
  simp only [symmetricStepHat, Chat, map_mul]

/-- The exact scalar coefficient multiplies identity in the production
symmetric continuous-linear-map representation. -/
theorem scalarSymmetric_operator_bridge (h : ℝ) :
    symmetricStepHat (1 : Mat 1) 1 h =
      scalarSymmetric h • (1 : E 1 →L[ℂ] E 1) := by
  have hm : scalarSymmetricMatrix h = scalarSymmetric h • (1 : Mat 1) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using scalarSymmetric_matrix_entry h
  calc
    symmetricStepHat (1 : Mat 1) 1 h =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1) (scalarSymmetricMatrix h) := by
      simp only [symmetricStepHat, Chat, scalarSymmetricMatrix, map_mul]
    _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
        (scalarSymmetric h • (1 : Mat 1)) := by rw [hm]
    _ = scalarSymmetric h • (1 : E 1 →L[ℂ] E 1) := by simp

theorem scalarSymmetric_two_re : (scalarSymmetric 2).re = -24 / 25 := by
  have hquarter : (2 : ℝ) / 4 = 1 / 2 := by norm_num
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarSymmetric, hquarter, hhalf, scalarCayley_half, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem scalarNonsymmetric_two_re : (scalarNonsymmetric 2).re = -1 := by
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarNonsymmetric, hhalf, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem scalarWrongQuarterStep_two_re : (scalarWrongQuarterStep 2).re = 0 := by
  have hhalf : (2 : ℝ) / 2 = 1 := by norm_num
  rw [scalarWrongQuarterStep, hhalf, scalarCayley_one]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- The symmetric composition is a different finite scheme even for
commuting scalar generators. This does not assert a rate obstruction. -/
theorem symmetric_vs_nonsymmetric_detected :
    scalarSymmetric 2 ≠ scalarNonsymmetric 2 := by
  intro h
  have hre := congrArg Complex.re h
  rw [scalarSymmetric_two_re, scalarNonsymmetric_two_re] at hre
  norm_num at hre

/-- Replacing the outer quarter-step parameters by half-step parameters
changes the exact scalar coefficient. -/
theorem wrong_quarterstep_detected :
    scalarSymmetric 2 ≠ scalarWrongQuarterStep 2 := by
  intro h
  have hre := congrArg Complex.re h
  rw [scalarSymmetric_two_re, scalarWrongQuarterStep_two_re] at hre
  norm_num at hre

private theorem scalarCayley_ne_neg_one (alpha : ℝ) : scalarCayley alpha ≠ -1 := by
  intro h
  have heq := (div_eq_iff (scalar_denominator_ne_zero alpha)).mp h
  have hre := congrArg Complex.re heq
  norm_num at hre

/-- At A=0, B=I, physical time π, and N=1, the symmetric matrix step has
the scalar entry C(π/2), which differs from the exact scalar exponential -1.
The preceding matrix bridge ties this product to `symmetricStepHat`.
This rejects finite equality; no small-step error-bound violation is asserted. -/
theorem finite_step_exponential_equality_rejected :
    (cayley (Real.pi / 4) (0 : Mat 1) * cayley (Real.pi / 2) 1 *
        cayley (Real.pi / 4) 0 : Mat 1) 0 0 ≠
      Complex.exp (-Complex.I * (Real.pi : ℂ)) := by
  have hzero : cayley (Real.pi / 4) (0 : Mat 1) = 1 := by
    simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]
  rw [hzero, one_mul, mul_one, scalarCayley_matrix_entry]
  have hexp : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    convert Complex.exp_neg_pi_mul_I using 1 <;> ring
  rw [hexp]
  exact scalarCayley_ne_neg_one (Real.pi / 2)

def pauliX : Mat 2 := !![0, 1; 1, 0]

def pauliZ : Mat 2 := !![1, 0; 0, -1]

theorem pauliX_hermitian : pauliX.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose_apply]

theorem pauli_noncommutation : ¬ Commute pauliX pauliZ := by
  intro h
  have h01 := congrFun (congrFun h.eq (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- After multiplying physical-time quadratic Taylor coefficients by minus
two, an ordered A B product has A²+B²+2AB; the exponential has (A+B)². The off-diagonal
entry of this Hermitian Pauli example proves these coefficients differ. -/
theorem nonsymmetric_quadratic_mismatch :
    pauliX ^ 2 + pauliZ ^ 2 + pauliX * pauliZ + pauliX * pauliZ ≠
      (pauliX + pauliZ) ^ 2 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.add_apply] at h01

end NDEAEvolve.Exp004.Controls

#print axioms NDEAEvolve.Exp004.Controls.zero_time_exact
#print axioms NDEAEvolve.Exp004.Controls.zero_power_identity
#print axioms NDEAEvolve.Exp004.Controls.zero_generators_exact
#print axioms NDEAEvolve.Exp004.Controls.zero_dimension_exact
#print axioms NDEAEvolve.Exp004.Controls.negative_time_bound
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_matrix_entry
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_one
#print axioms NDEAEvolve.Exp004.Controls.scalarCayley_half
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_matrix_entry
#print axioms NDEAEvolve.Exp004.Controls.symmetricStepHat_matrix_bridge
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_operator_bridge
#print axioms NDEAEvolve.Exp004.Controls.scalarSymmetric_two_re
#print axioms NDEAEvolve.Exp004.Controls.scalarNonsymmetric_two_re
#print axioms NDEAEvolve.Exp004.Controls.scalarWrongQuarterStep_two_re
#print axioms NDEAEvolve.Exp004.Controls.symmetric_vs_nonsymmetric_detected
#print axioms NDEAEvolve.Exp004.Controls.wrong_quarterstep_detected
#print axioms NDEAEvolve.Exp004.Controls.finite_step_exponential_equality_rejected
#print axioms NDEAEvolve.Exp004.Controls.pauliX_hermitian
#print axioms NDEAEvolve.Exp004.Controls.pauliZ_hermitian
#print axioms NDEAEvolve.Exp004.Controls.pauli_noncommutation
#print axioms NDEAEvolve.Exp004.Controls.nonsymmetric_quadratic_mismatch
-- END /home/richman954/NDEA_Evolve_offruntime/exp004/worktree/NDEA_Evolve/experiments/exp004_symmetric_cayley_second_order/controls/lean/NegativeControls.lean
