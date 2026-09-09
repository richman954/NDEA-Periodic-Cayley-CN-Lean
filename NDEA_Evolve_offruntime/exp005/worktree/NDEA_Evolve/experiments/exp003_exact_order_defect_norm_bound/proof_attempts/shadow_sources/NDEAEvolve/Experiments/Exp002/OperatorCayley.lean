/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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
