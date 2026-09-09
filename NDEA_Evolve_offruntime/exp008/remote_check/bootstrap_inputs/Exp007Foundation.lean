import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- SOURCE foundation/Exp006CombinedVerification.lean SHA256 af3d14716b492f6485dd1bcf88c3c99cd13440a219f89b27b5258531d7f96c52

-- SOURCE Exp005Foundation.lean SHA256 40386d3848f338f4ea89869a39a920e127674f5a42a471dfbd969901599a8785

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean SHA256 0849ce5520b2582112b733d681b7901a64cf45d82a37a53605194c6147e2a15f
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
-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp002/OperatorCayley.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean SHA256 419451c84966173a2db4020c7f8fcb29d4e6bce6dbcc77640fcc6e09835fbe05
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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/experiments/exp003_exact_order_defect_norm_bound/proof_attempts/shadow_sources/NDEAEvolve/Experiments/Exp003/EuclideanResolventContraction.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean SHA256 216a8625424d696ff5c5716d8fd2712ec6041dca54442de9e5bcef31a895024d

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactOrderDefectNormBound.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean SHA256 be1cfe32010bebc8b87b0982480a33d61f4d5ada9ccb19aa03a668699954e8b5

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExactSplitUnsplitCayleyDefect.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean SHA256 afd2134c867b75a648f159aad3a321f11fe2e352d98d24a6574c4da9e3a70aea

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/FiniteNTelescopingGlobalBound.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExponentialRemainder.lean SHA256 6d56da15466b7c6920916a72a0eb66daf209442ecf3d3170468eb78ad323b747

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ExponentialRemainder.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialComparison.lean SHA256 e7ec9be08d19d315d6c0cffab4f74ec47d650c1a1344cae3469e9596c84cdb85

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialComparison.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialLimit.lean SHA256 f009e79daa8f4728743fa8d6ca6f879dc990a66ab2d9ab5535d9186120bde333

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp003/ContinuousExponentialLimit.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyLocal.lean SHA256 776ddc1a68ed1e4acf8e2c587916ed45240542d7fa93fd5106a49685bde9d8e3

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyLocal.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyGlobal.lean SHA256 f4a02fabef86b256f8d4b31f9be657aebeb8f263c2b52d4c2afa53c314a65060

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

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp004/SymmetricCayleyGlobal.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/MeshWeightedStability.lean SHA256 9d1c974c142e65b50124e01d25f4cb3acf553e40a0980980dfd04dce8c090602

/-!
# Mesh-weighted stability and measured trajectory defects

The weight is the square root of a real mesh parameter, multiplying the
existing Euclidean norm. Stability and accumulation are algebraic consequences
of the symmetric step's unconditional unitarity. No generator-norm bound or
small-step hypothesis is used here.

The fixed-time estimate takes a bound on the actual trajectory defect as an
explicit premise. It does not derive that premise from a differential equation.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

def weightedNorm {n : ℕ} (dx : ℝ) (x : E n) : ℝ :=
  Real.sqrt dx * ‖x‖

theorem weightedNorm_nonneg {n : ℕ} (dx : ℝ) (x : E n) :
    0 ≤ weightedNorm dx x :=
  mul_nonneg (Real.sqrt_nonneg dx) (norm_nonneg x)

@[simp]
theorem weightedNorm_zero (dx : ℝ) (n : ℕ) :
    weightedNorm dx (0 : E n) = 0 := by
  simp [weightedNorm]

@[simp]
theorem weightedNorm_neg {n : ℕ} (dx : ℝ) (x : E n) :
    weightedNorm dx (-x) = weightedNorm dx x := by
  simp [weightedNorm]

theorem weightedNorm_sub_rev {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x - y) = weightedNorm dx (y - x) := by
  unfold weightedNorm
  rw [norm_sub_rev]

theorem weightedNorm_add_le {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x + y) ≤ weightedNorm dx x + weightedNorm dx y := by
  unfold weightedNorm
  calc
    Real.sqrt dx * ‖x + y‖ ≤ Real.sqrt dx * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le x y) (Real.sqrt_nonneg dx)
    _ = Real.sqrt dx * ‖x‖ + Real.sqrt dx * ‖y‖ := by ring

theorem weightedNorm_sub_le {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x - y) ≤ weightedNorm dx x + weightedNorm dx y := by
  simpa only [sub_eq_add_neg, weightedNorm_neg] using
    weightedNorm_add_le dx x (-y)

theorem weightedNorm_smul {n : ℕ} (dx : ℝ) (c : ℂ) (x : E n) :
    weightedNorm dx (c • x) = ‖c‖ * weightedNorm dx x := by
  simp only [weightedNorm, norm_smul]
  ring

theorem weightedNorm_real_smul {n : ℕ} (dx k : ℝ) (x : E n) :
    weightedNorm dx (k • x) = |k| * weightedNorm dx x := by
  simp only [weightedNorm, norm_smul, Real.norm_eq_abs]
  ring

theorem weightedNorm_eq_zero_iff {n : ℕ} (dx : ℝ) (hdx : 0 < dx) (x : E n) :
    weightedNorm dx x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsqrt : Real.sqrt dx ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdx)
    have hx : ‖x‖ = 0 := (mul_eq_zero.mp h).resolve_left hsqrt
    exact norm_eq_zero.mp hx
  · rintro rfl
    exact weightedNorm_zero dx n

/-- The weighted norm is preserved for every real symmetric time step and
every finite dimension. The mesh parameter need not bound the generators. -/
theorem symmetricStepHat_weightedNorm_preserved {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (x : E n) :
    weightedNorm dx (symmetricStepHat A B k x) = weightedNorm dx x := by
  unfold weightedNorm
  rw [ContinuousLinearMap.norm_map_of_mem_unitary
    (symmetricStepHat_mem_unitary k A B hA hB) x]

theorem symmetricStepHat_weighted_distance_preserved {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (x y : E n) :
    weightedNorm dx
        (symmetricStepHat A B k x - symmetricStepHat A B k y) =
      weightedNorm dx (x - y) := by
  rw [← map_sub]
  exact symmetricStepHat_weightedNorm_preserved dx k A B hA hB (x - y)

/-- The discrepancy of a supplied reference trajectory from one actual
symmetric numerical step, with its sign and argument order fixed. -/
def trajectoryDefect {n : ℕ} (A B : Mat n) (k : ℝ)
    (u : ℕ → E n) (j : ℕ) : E n :=
  u (j + 1) - symmetricStepHat A B k (u j)

theorem trajectoryDefect_recurrence {n : ℕ} (A B : Mat n) (k : ℝ)
    (u : ℕ → E n) (j : ℕ) :
    u (j + 1) = symmetricStepHat A B k (u j) + trajectoryDefect A B k u j := by
  unfold trajectoryDefect
  abel

/-- Actual trajectory defects accumulate without amplification in the
mesh-weighted norm. This theorem includes the empty sum at N=0. -/
theorem symmetric_weighted_error_accumulation {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) :
    weightedNorm dx (u N - v N) ≤
      weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [trajectoryDefect_recurrence A B k u N, hv N]
      calc
        weightedNorm dx
            (symmetricStepHat A B k (u N) + trajectoryDefect A B k u N -
              symmetricStepHat A B k (v N)) =
            weightedNorm dx
              ((symmetricStepHat A B k (u N) - symmetricStepHat A B k (v N)) +
                trajectoryDefect A B k u N) := by
          congr 1
          abel
        _ ≤ weightedNorm dx
              (symmetricStepHat A B k (u N) - symmetricStepHat A B k (v N)) +
            weightedNorm dx (trajectoryDefect A B k u N) :=
          weightedNorm_add_le _ _ _
        _ = weightedNorm dx (u N - v N) +
            weightedNorm dx (trajectoryDefect A B k u N) := by
          rw [symmetricStepHat_weighted_distance_preserved dx k A B hA hB]
        _ ≤ (weightedNorm dx (u 0 - v 0) +
              ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j)) +
            weightedNorm dx (trajectoryDefect A B k u N) :=
          add_le_add ih (le_refl _)
        _ = weightedNorm dx (u 0 - v 0) +
              ∑ j ∈ Finset.range (N + 1),
                weightedNorm dx (trajectoryDefect A B k u j) := by
          rw [Finset.sum_range_succ]
          ring

/-- A supplied space-time residual estimate yields a fixed-time error
certificate for the actual symmetric recurrence. Uniformity across meshes
requires the constants in this explicit premise to be uniform. -/
theorem symmetric_weighted_fixed_time_error {n : ℕ}
    (dx k T Ct Cs : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) (hk : 0 ≤ k) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hdefect : ∀ j : ℕ, j < N →
      weightedNorm dx (trajectoryDefect A B k u j) ≤
        k * (Ct * k ^ 2 + Cs * dx ^ 2)) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
  have hrate : 0 ≤ Ct * k ^ 2 + Cs * dx ^ 2 :=
    add_nonneg (mul_nonneg hCt (sq_nonneg k))
      (mul_nonneg hCs (sq_nonneg dx))
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  calc
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) :=
      symmetric_weighted_error_accumulation dx k A B hA hB u v hv N
    _ ≤ weightedNorm dx (u 0 - v 0) +
        ∑ _j ∈ Finset.range N, k * (Ct * k ^ 2 + Cs * dx ^ 2) := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro j hj
      exact hdefect j (Finset.mem_range.mp hj)
    _ = weightedNorm dx (u 0 - v 0) +
        (N : ℝ) * (k * (Ct * k ^ 2 + Cs * dx ^ 2)) := by simp
    _ ≤ weightedNorm dx (u 0 - v 0) +
        T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
      apply add_le_add (le_refl _)
      rw [← mul_assoc]
      exact mul_le_mul horizon (le_refl _) hrate hT

/-- A uniform pointwise residual bound becomes a weighted Euclidean bound
depending on the physical length, with no dimension factor. Zero dimension
is included when the cardinality/mesh identity forces L=0. -/
theorem weightedNorm_of_pointwise_bound {n : ℕ}
    (dx L R : ℝ) (hdx : 0 ≤ dx) (hL : 0 ≤ L)
    (hcard : (n : ℝ) * dx = L) (r : Fin n → ℂ)
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) :
    weightedNorm dx (WithLp.toLp 2 r) ≤ Real.sqrt L * R := by
  have hsquared : weightedNorm dx (WithLp.toLp 2 r) ^ 2 ≤ L * R ^ 2 := by
    rw [weightedNorm, mul_pow, Real.sq_sqrt hdx, EuclideanSpace.norm_sq_eq]
    change dx * ∑ i : Fin n, ‖r i‖ ^ 2 ≤ L * R ^ 2
    calc
      dx * ∑ i : Fin n, ‖r i‖ ^ 2 ≤ dx * ∑ _i : Fin n, R ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hdx
        apply Finset.sum_le_sum
        intro i _hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hr i) 2
      _ = dx * ((n : ℝ) * R ^ 2) := by simp
      _ = L * R ^ 2 := by rw [← hcard]; ring
  have hright : (Real.sqrt L * R) ^ 2 = L * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL]
  have hleftNonneg := weightedNorm_nonneg dx (WithLp.toLp 2 r)
  have hrightNonneg := mul_nonneg (Real.sqrt_nonneg L) hR
  nlinarith

end NDEAEvolve.Exp005

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/MeshWeightedStability.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/SymmetricStageResidual.lean SHA256 469a9a8428c5345dcd7d29a7ed7e08ecd00a6d0e35382b6b3b29d5402308f5a2

/-!
# Measured stage residuals for the symmetric Cayley scheme

Each factor residual is defined from its supplied source and target states.
An exact ordered identity transfers the three measured residuals to the
full-step discrepancy. Unitarity and resolvent contraction bound the transfer
with constant one, independently of the mesh and generator norms.

The fixed-time corollary assumes an explicit estimate on these actual stage
residuals. It does not derive that estimate from smooth PDE solutions.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

abbrev denominatorHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  operatorOf (cayleyD alpha H)

abbrev numeratorHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  operatorOf (cayleyN alpha H)

/-- The measured residual of one implicit Cayley factor, with no implicit
time-step scaling: denominator times target minus numerator times source. -/
def factorResidual {n : ℕ} (H : Mat n) (alpha : ℝ)
    (source target : E n) : E n :=
  denominatorHat H alpha target - numeratorHat H alpha source

private theorem inverse_mul_numerator {R : Type*} [Ring R]
    (X RX : R) (hLeft : RX * (1 + X) = 1) (hRight : (1 + X) * RX = 1) :
    RX * (1 - X) = (1 - X) * RX := by
  calc
    RX * (1 - X) = RX + RX - RX * (1 + X) := by noncomm_ring
    _ = RX + RX - 1 := by rw [hLeft]
    _ = RX + RX - (1 + X) * RX := by rw [hRight]
    _ = (1 - X) * RX := by noncomm_ring

theorem resolvent_mul_denominatorHat {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    Rhat H alpha * denominatorHat H alpha = 1 := by
  simpa only [Rhat, denominatorHat, operatorOf, map_mul, map_one] using
    congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayleyR_mul_cayleyD alpha H hH)

theorem resolvent_mul_numeratorHat {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    Rhat H alpha * numeratorHat H alpha = Chat H alpha := by
  have hLeft : cayleyR alpha H * (1 + skewPart alpha H) = 1 :=
    cayleyR_mul_cayleyD alpha H hH
  have hRight : (1 + skewPart alpha H) * cayleyR alpha H = 1 :=
    cayleyD_mul_cayleyR alpha H hH
  have hm : cayleyR alpha H * cayleyN alpha H = cayley alpha H :=
    inverse_mul_numerator (skewPart alpha H) (cayleyR alpha H) hLeft hRight
  simpa only [Rhat, numeratorHat, Chat, operatorOf, map_mul] using
    congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M) hm

/-- Exact conversion of the measured implicit-factor residual to a
one-factor state discrepancy. -/
theorem resolvent_factorResidual {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian)
    (source target : E n) :
    Rhat H alpha (factorResidual H alpha source target) =
      target - Chat H alpha source := by
  calc
    Rhat H alpha (factorResidual H alpha source target) =
        (Rhat H alpha * denominatorHat H alpha) target -
          (Rhat H alpha * numeratorHat H alpha) source := by
      simp only [factorResidual, map_sub, ContinuousLinearMap.mul_apply]
    _ = target - Chat H alpha source := by
      rw [resolvent_mul_denominatorHat alpha H hH,
        resolvent_mul_numeratorHat alpha H hH]
      rfl

theorem factorResidual_recurrence {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian)
    (source target : E n) :
    target = Chat H alpha source + Rhat H alpha (factorResidual H alpha source target) := by
  rw [resolvent_factorResidual alpha H hH source target]
  abel

/-- The sum of the three actual factor-residual norms. Each occurrence uses
the corresponding Cayley parameter k/4, k/2, k/4. -/
def stageResidualBudget {n : ℕ} (dx k : ℝ) (A B : Mat n)
    (source first second target : E n) : ℝ :=
  weightedNorm dx (factorResidual A (k / 4) source first) +
    weightedNorm dx (factorResidual B (k / 2) first second) +
    weightedNorm dx (factorResidual A (k / 4) second target)

theorem stageResidualBudget_nonneg {n : ℕ} (dx k : ℝ) (A B : Mat n)
    (source first second target : E n) :
    0 ≤ stageResidualBudget dx k A B source first second target :=
  add_nonneg (add_nonneg (weightedNorm_nonneg _ _) (weightedNorm_nonneg _ _))
    (weightedNorm_nonneg _ _)

/-- Ordered transfer of all three measured stage residuals. The first
residual passes through both later factors; the middle passes through the
last factor; the last is only resolved by its own inverse denominator. -/
theorem symmetric_stage_residual_identity {n : ℕ}
    (k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (source first second target : E n) :
    target - symmetricStepHat A B k source =
      Chat A (k / 4) (Chat B (k / 2)
        (Rhat A (k / 4) (factorResidual A (k / 4) source first))) +
      Chat A (k / 4) (Rhat B (k / 2) (factorResidual B (k / 2) first second)) +
      Rhat A (k / 4) (factorResidual A (k / 4) second target) := by
  let r1 := factorResidual A (k / 4) source first
  let r2 := factorResidual B (k / 2) first second
  let r3 := factorResidual A (k / 4) second target
  have h1 : first = Chat A (k / 4) source + Rhat A (k / 4) r1 :=
    factorResidual_recurrence (k / 4) A hA source first
  have h2 : second = Chat B (k / 2) first + Rhat B (k / 2) r2 :=
    factorResidual_recurrence (k / 2) B hB first second
  have h3 : target = Chat A (k / 4) second + Rhat A (k / 4) r3 :=
    factorResidual_recurrence (k / 4) A hA second target
  change target - symmetricStepHat A B k source =
    Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1)) +
      Chat A (k / 4) (Rhat B (k / 2) r2) + Rhat A (k / 4) r3
  calc
    target - symmetricStepHat A B k source =
        (Chat A (k / 4)
          (Chat B (k / 2) (Chat A (k / 4) source + Rhat A (k / 4) r1) +
            Rhat B (k / 2) r2) + Rhat A (k / 4) r3) -
          Chat A (k / 4) (Chat B (k / 2) (Chat A (k / 4) source)) := by
      rw [← h1, ← h2, ← h3]
      rfl
    _ = _ := by
      simp only [map_add]
      abel

theorem cayley_weightedNorm_preserved {n : ℕ}
    (dx alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) (x : E n) :
    weightedNorm dx (Chat H alpha x) = weightedNorm dx x := by
  unfold weightedNorm
  rw [cayley_preserves_norm alpha H hH x]

theorem resolvent_weightedNorm_le {n : ℕ}
    (dx alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) (x : E n) :
    weightedNorm dx (Rhat H alpha x) ≤ weightedNorm dx x := by
  unfold weightedNorm
  exact mul_le_mul_of_nonneg_left
    (cayleyR_toEuclideanCLM_apply_norm_le alpha H hH x) (Real.sqrt_nonneg dx)

/-- The measured residuals bound the actual full-step discrepancy with
constant one and no step-size or operator-norm restriction. -/
theorem symmetric_stage_residual_weighted_le {n : ℕ}
    (dx k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (source first second target : E n) :
    weightedNorm dx (target - symmetricStepHat A B k source) ≤
      stageResidualBudget dx k A B source first second target := by
  let r1 := factorResidual A (k / 4) source first
  let r2 := factorResidual B (k / 2) first second
  let r3 := factorResidual A (k / 4) second target
  let d1 := Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1))
  let d2 := Chat A (k / 4) (Rhat B (k / 2) r2)
  let d3 := Rhat A (k / 4) r3
  have h1 : weightedNorm dx d1 ≤ weightedNorm dx r1 := by
    change weightedNorm dx (Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1))) ≤ _
    rw [cayley_weightedNorm_preserved dx (k / 4) A hA,
      cayley_weightedNorm_preserved dx (k / 2) B hB]
    exact resolvent_weightedNorm_le dx (k / 4) A hA r1
  have h2 : weightedNorm dx d2 ≤ weightedNorm dx r2 := by
    change weightedNorm dx (Chat A (k / 4) (Rhat B (k / 2) r2)) ≤ _
    rw [cayley_weightedNorm_preserved dx (k / 4) A hA]
    exact resolvent_weightedNorm_le dx (k / 2) B hB r2
  have h3 : weightedNorm dx d3 ≤ weightedNorm dx r3 :=
    resolvent_weightedNorm_le dx (k / 4) A hA r3
  rw [symmetric_stage_residual_identity k A B hA hB]
  change weightedNorm dx (d1 + d2 + d3) ≤
    weightedNorm dx r1 + weightedNorm dx r2 + weightedNorm dx r3
  calc
    _ ≤ weightedNorm dx (d1 + d2) + weightedNorm dx d3 := weightedNorm_add_le _ _ _
    _ ≤ (weightedNorm dx d1 + weightedNorm dx d2) + weightedNorm dx d3 :=
      add_le_add (weightedNorm_add_le dx d1 d2) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

/-- Global a posteriori error certificate for the actual symmetric numerical
trajectory v and supplied reference/stage states. N=0 is included. -/
theorem symmetric_stage_residual_accumulation {n : ℕ}
    (dx k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v first second : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j)) (N : ℕ) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      ∑ j ∈ Finset.range N,
        stageResidualBudget dx k A B (u j) (first j) (second j) (u (j + 1)) := by
  calc
    _ ≤ weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) :=
      symmetric_weighted_error_accumulation dx k A B hA hB u v hv N
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro j _hj
      exact symmetric_stage_residual_weighted_le dx k A B hA hB
        (u j) (first j) (second j) (u (j + 1))

/-- Conditional space-time error estimate from a mesh-uniform bound on the
sum of the actual stage residuals. Establishing that premise for sampled
smooth PDE solutions is a separate consistency problem. -/
theorem symmetric_stage_residual_fixed_time_error {n : ℕ}
    (dx k T Ct Cs : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v first second : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) (hk : 0 ≤ k) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hbudget : ∀ j : ℕ, j < N →
      stageResidualBudget dx k A B (u j) (first j) (second j) (u (j + 1)) ≤
        k * (Ct * k ^ 2 + Cs * dx ^ 2)) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
  apply symmetric_weighted_fixed_time_error dx k T Ct Cs A B hA hB u v hv N
    hk hCt hCs horizon
  intro j hj
  exact (symmetric_stage_residual_weighted_le dx k A B hA hB
    (u j) (first j) (second j) (u (j + 1))).trans (hbudget j hj)

end NDEAEvolve.Exp005

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/SymmetricStageResidual.lean

-- BEGIN /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/MeshFamilyConvergence.lean SHA256 557152220ef0871da427e97ebffb64a244d8ea6a462c2f62db6f108333326cec

/-!
# Conditional convergence of mesh-weighted errors on varying finite spaces

The dimensions and Hermitian matrices may depend on the refinement index.
The conclusion is convergence of the scalar weighted error; it does not
identify different finite-dimensional state spaces or assert convergence of
interpolants in a common function space. Uniform residual bounds remain
explicit premises, not consequences of stability or of fixed-matrix Exp004.
-/

noncomputable section

open Filter
open scoped Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

/-- A common space-time residual majorant vanishes under mesh refinement. -/
theorem mesh_error_majorant_tendsto_zero
    (k dx initial : ℕ → ℝ) (T Ct Cs : ℝ)
    (hk : Tendsto k atTop (𝓝 0)) (hdx : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto initial atTop (𝓝 0)) :
    Tendsto (fun q => initial q + T * (Ct * k q ^ 2 + Cs * dx q ^ 2))
      atTop (𝓝 0) := by
  simpa using hinitial.add
    ((tendsto_const_nhds (x := T)).mul
      (((tendsto_const_nhds (x := Ct)).mul (hk.pow 2)).add
        ((tendsto_const_nhds (x := Cs)).mul (hdx.pow 2))))

/-- Conditional mesh-family convergence from the actual trajectory defects.
The constants Ct, Cs, T are common across all refinement indices; generator
norms and dimensions are unrestricted. Physical spacings are positive. -/
theorem symmetric_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (dx k : ℕ → ℝ) (T Ct Cs : ℝ)
    (A B : (q : ℕ) → Mat (n q))
    (hA : ∀ q, (A q).IsHermitian) (hB : ∀ q, (B q).IsHermitian)
    (u v : (q : ℕ) → ℕ → E (n q))
    (hv : ∀ q j, v q (j + 1) = symmetricStepHat (A q) (B q) (k q) (v q j))
    (hdx : ∀ q, 0 < dx q) (hk : ∀ q, 0 ≤ k q)
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : ∀ q, (N q : ℝ) * k q ≤ T)
    (hdefect : ∀ q j, j < N q →
      weightedNorm (dx q) (trajectoryDefect (A q) (B q) (k q) (u q) j) ≤
        k q * (Ct * k q ^ 2 + Cs * dx q ^ 2))
    (hk_limit : Tendsto k atTop (𝓝 0)) (hdx_limit : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto (fun q => weightedNorm (dx q) (u q 0 - v q 0))
      atTop (𝓝 0)) :
    Tendsto (fun q => weightedNorm (dx q) (u q (N q) - v q (N q)))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun q => weightedNorm_nonneg (dx q) (u q (N q) - v q (N q)))
  · intro q
    exact symmetric_weighted_fixed_time_error (dx q) (k q) T Ct Cs
      (A q) (B q) (hA q) (hB q) (u q) (v q) (hv q) (N q)
      (hk q) hCt hCs (horizon q) (hdefect q)
  · exact mesh_error_majorant_tendsto_zero k dx _ T Ct Cs
      hk_limit hdx_limit hinitial

/-- Conditional convergence using the three measured factor residuals of
the actual symmetric Cayley stages. This is the PDE-facing transfer endpoint;
deriving its uniform hbudget premise for a smooth split PDE is separate work. -/
theorem symmetric_stage_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (dx k : ℕ → ℝ) (T Ct Cs : ℝ)
    (A B : (q : ℕ) → Mat (n q))
    (hA : ∀ q, (A q).IsHermitian) (hB : ∀ q, (B q).IsHermitian)
    (u v first second : (q : ℕ) → ℕ → E (n q))
    (hv : ∀ q j, v q (j + 1) = symmetricStepHat (A q) (B q) (k q) (v q j))
    (hdx : ∀ q, 0 < dx q) (hk : ∀ q, 0 ≤ k q)
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : ∀ q, (N q : ℝ) * k q ≤ T)
    (hbudget : ∀ q j, j < N q →
      stageResidualBudget (dx q) (k q) (A q) (B q)
        (u q j) (first q j) (second q j) (u q (j + 1)) ≤
          k q * (Ct * k q ^ 2 + Cs * dx q ^ 2))
    (hk_limit : Tendsto k atTop (𝓝 0)) (hdx_limit : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto (fun q => weightedNorm (dx q) (u q 0 - v q 0))
      atTop (𝓝 0)) :
    Tendsto (fun q => weightedNorm (dx q) (u q (N q) - v q (N q)))
      atTop (𝓝 0) := by
  apply symmetric_mesh_family_error_tendsto_zero n N dx k T Ct Cs A B hA hB
    u v hv hdx hk hCt hCs horizon
  · intro q j hj
    exact (symmetric_stage_residual_weighted_le (dx q) (k q) (A q) (B q)
      (hA q) (hB q) (u q j) (first q j) (second q j) (u q (j + 1))).trans
        (hbudget q j hj)
  · exact hk_limit
  · exact hdx_limit
  · exact hinitial

end NDEAEvolve.Exp005

-- END /home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve/NDEAEvolve/Experiments/Exp005/MeshFamilyConvergence.lean

-- SOURCE PeriodicGrid.lean SHA256 674318480a8ce5fe52f6a2660fddfd4cfd0e9b2c26c7fc6ee3a2817a110c7222

/-! Minimal finite periodic grid, Hermitian centered negative Laplacian,
and its action on samples of a periodic function.  The endpoint wrap is
proved explicitly from the period and mesh identity. -/

noncomputable section
open Matrix Complex
namespace NDEAEvolve.Exp006.PeriodicGrid

abbrev next {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) := finRotate (n + 1) i

abbrev prev {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  (finRotate (n + 1)).symm i

def sample {n : ℕ} (h : ℝ) (f : ℝ → ℂ) : Fin (n + 1) → ℂ :=
  fun i => f ((i.val : ℝ) * h)

def shiftMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (finRotate (n + 1)).permMatrix ℂ

/-- Centered negative second difference, including the periodic corner entries. -/
def laplacian (n : ℕ) (h : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ((h : ℂ) ^ 2)⁻¹ •
    ((2 : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      shiftMatrix n - (shiftMatrix n)ᴴ)

theorem isHermitian (n : ℕ) (h : ℝ) : (laplacian n h).IsHermitian := by
  unfold laplacian Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    star_inv₀, star_pow, Complex.star_def, Complex.conj_ofReal,
    map_ofNat]
  congr 1
  abel

theorem laplacian_mulVec {n : ℕ} (h : ℝ) (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) :
    (laplacian n h).mulVec v i =
      (2 * v i - v (next i) - v (prev i)) / (h : ℂ)^2 := by
  simp only [laplacian, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, shiftMatrix, Matrix.conjTranspose_permMatrix,
    Matrix.permMatrix_mulVec, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Function.comp_apply, Equiv.Perm.inv_def, next, prev]
  ring

theorem sample_next {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) : sample h f (next i) = f ((i.val : ℝ) * h + h) := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [next, finRotate_last, sample, Fin.val_zero, Fin.val_last,
      Nat.cast_zero, zero_mul]
    have hcoord : (n : ℝ) * h + h = L := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hmesh
    rw [hcoord]
    simpa using (hf 0).symm
  · change f (((finRotate (n + 1) i).val : ℝ) * h) = _
    rw [coe_finRotate_of_ne_last hi, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem sample_prev {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) : sample h f (prev i) = f ((i.val : ℝ) * h - h) := by
  by_cases hi : i = 0
  · subst i
    have hprev : prev (0 : Fin (n + 1)) = Fin.last n := by
      apply (finRotate (n + 1)).injective
      simp only [prev, Equiv.apply_symm_apply, finRotate_last]
    rw [hprev]
    simp only [sample, Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_mul, zero_sub]
    have hcoord : -h + L = (n : ℝ) * h := by
      calc
        -h + L = -h + (((n + 1 : ℕ) : ℝ)) * h := by rw [hmesh]
        _ = (n : ℝ) * h := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [← hcoord]
    exact hf (-h)
  · change f ((((finRotate (n + 1)).symm i).val : ℝ) * h) = _
    have hival : i.val ≠ 0 := by
      intro hzero
      apply hi
      apply Fin.ext
      simpa using hzero
    have hone : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hival
    rw [coe_finRotate_symm_of_ne_zero hi, Nat.cast_sub hone, Nat.cast_one]
    congr 1
    ring

/-- The matrix really applies the unwrapped centered stencil to periodic samples,
including the first and last rows. No condition on the sample function is omitted. -/
theorem matrix_sample_stencil {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) :
    (laplacian n h).mulVec (sample h f) i =
      (2 * f ((i.val : ℝ) * h) - f ((i.val : ℝ) * h + h) -
        f ((i.val : ℝ) * h - h)) / (h : ℂ)^2 := by
  rw [laplacian_mulVec, sample_next L h f hf hmesh,
    sample_prev L h f hf hmesh]
  rfl


end NDEAEvolve.Exp006.PeriodicGrid

-- SOURCE PeriodicModeResidual.lean SHA256 8f4b178578089c2c60d9945e8d48e5326f8a9e2e4e4a30f2cf1d6570cb1b6b3a

/-! Concrete periodic split-Schrodinger residual. No residual bound is assumed.
The physical mode is nonconstant and both split generators act nontrivially.
This is a commuting, single-mode milestone; it is not a general PDE closure. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp006

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by simp [phase]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_formula (x : ℝ) :
    phase x = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  exact Complex.exp_ofReal_mul_I x

def mode (t x : ℝ) : ℂ := phase (x - 2*t)

 theorem phase_periodic : Function.Periodic phase (2*Real.pi) := by
  intro x
  simpa [phase, Complex.ofReal_add, Complex.ofReal_mul] using
    Complex.exp_mul_I_periodic (x : ℂ)

 theorem mode_periodic (t : ℝ) : Function.Periodic (mode t) (2*Real.pi) := by
  intro x
  change phase ((x+2*Real.pi)-2*t) = phase (x-2*t)
  rw [show (x+2*Real.pi)-2*t = (x-2*t)+2*Real.pi by ring]
  exact phase_periodic (x-2*t)

 theorem phase_hasDerivAt (x : ℝ) : HasDerivAt phase (phase x * Complex.I) x := by
  simpa [phase] using! (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).cexp).comp_ofReal

 theorem mode_space_hasDerivAt (t x : ℝ) :
    HasDerivAt (mode t) (mode t x * Complex.I) x := by
  change HasDerivAt (fun y => phase (y-2*t)) (phase (x-2*t)*Complex.I) x
  simpa [mode, Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using! (phase_hasDerivAt (x-2*t)).scomp x ((hasDerivAt_id x).sub_const (2*t))

 theorem mode_time_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun s => mode s x) (mode t x * Complex.I * (-2)) t := by
  simpa [mode, Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using! (phase_hasDerivAt (x-2*t)).scomp t
    ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul 2))

 theorem mode_second_derivative (t x : ℝ) : deriv (deriv (mode t)) x = - mode t x := by
  have hd : deriv (mode t) = fun y => mode t y * Complex.I :=
    funext fun y => (mode_space_hasDerivAt t y).deriv
  rw [hd, ((mode_space_hasDerivAt t x).mul_const Complex.I).deriv]
  simp [mul_assoc]

 /-- The displayed PDE is checked with genuine real derivatives. -/
 theorem mode_solves_split_schrodinger (t x : ℝ) :
    Complex.I * deriv (fun s => mode s x) t = -2 * deriv (deriv (mode t)) x := by
  rw [(mode_time_hasDerivAt t x).deriv, mode_second_derivative]
  calc
    _ = (Complex.I*Complex.I) * (-2) * mode t x := by ring
    _ = _ := by simp

 theorem mode_nonzero (t x : ℝ) : mode t x ≠ 0 := by
  exact Complex.exp_ne_zero _

 theorem mode_nonconstant (t : ℝ) : ∃ x y, mode t x ≠ mode t y := by
  refine ⟨2*t, 2*t+Real.pi, ?_⟩
  simp only [mode, phase, show 2*t-2*t=0 by ring,
    show 2*t+Real.pi-2*t=Real.pi by ring]
  norm_num [Complex.exp_pi_mul_I]

def spatialSymbol (h : ℝ) : ℝ := (2 - 2 * Real.cos h) / h^2

/-- The actual centered negative second difference on an unwrapped sample.
For the periodic mode, unwrapped and periodically wrapped samples agree. -/
def centeredStencil (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 * f x - f (x+h) - f (x-h)) / (h : ℂ)^2

theorem phase_centeredStencil (h x : ℝ) :
    centeredStencil h phase x = (spatialSymbol h : ℂ) * phase x := by
  have hadd : phase (x+h) = phase x * phase h := phase_add x h
  have hsub : phase (x-h) = phase x * phase (-h) := by
    simpa [sub_eq_add_neg] using phase_add x (-h)
  have hsum : phase h + phase (-h) = (2 * Real.cos h : ℝ) := by
    rw [phase_formula, phase_formula]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  unfold centeredStencil spatialSymbol
  rw [hadd, hsub]
  push_cast
  calc
    _ = (2 - (phase h + phase (-h))) / (h : ℂ)^2 * phase x := by ring
    _ = _ := by rw [hsum]; push_cast; ring

/-- A concrete mesh-uniform spatial estimate, from the library cosine Taylor
remainder. The 1/8 constant is deliberately rounded upward. -/
theorem spatialSymbol_consistency (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1) :
    |spatialSymbol h - 1| ≤ h^2 / 8 := by
  have hc := Real.cos_bound (x := h) (by rwa [abs_of_pos hh])
  rw [abs_of_pos hh] at hc
  have hid : spatialSymbol h - 1 = -2 * (Real.cos h - (1 - h^2/2)) / h^2 := by
    unfold spatialSymbol
    field_simp
    <;> ring
  rw [hid, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hh)]
  norm_num
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  nlinarith [sq_nonneg (h^2)]

/-- On every nonzero mesh the first Fourier symbol has genuine spatial error. -/
theorem spatialSymbol_strictly_below_continuum (h : ℝ) (hh : h ≠ 0) :
    spatialSymbol h < 1 := by
  unfold spatialSymbol
  apply (div_lt_one (sq_pos_of_ne_zero hh)).2
  have hc := Real.one_sub_sq_div_two_lt_cos hh
  nlinarith

theorem sin_linear_remainder (a : ℝ) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    |Real.sin a - a| ≤ a^3/4 := by
  have hs := Real.sin_bound (x := a) (by rwa [abs_of_nonneg ha])
  rw [abs_of_nonneg ha] at hs
  have hp : a^4 ≤ a^3 := by
    calc
      a^4 = a^3*a := by ring
      _ ≤ a^3*1 := mul_le_mul_of_nonneg_left hasmall (pow_nonneg ha _)
      _ = a^3 := mul_one _
  have htri : |Real.sin a - a| ≤ |Real.sin a - (a-a^3/6)| + a^3/6 := by
    calc
      _ = |(Real.sin a - (a-a^3/6)) + (-(a^3/6))| := by congr 1; ring
      _ ≤ |Real.sin a - (a-a^3/6)| + |-(a^3/6)| := abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_of_nonneg (show 0 ≤ a^3/6 by positivity)]
  nlinarith [pow_nonneg ha 3]

theorem cos_linear_remainder (a : ℝ) : |Real.cos a - 1| ≤ a^2/2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one a))]
  have h := Real.one_sub_sq_div_two_le_cos (x := a)
  linarith

theorem midpoint_temporal_remainder (a : ℝ) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    |a * Real.cos a - Real.sin a| ≤ a^3 := by
  calc
    _ = |a * (Real.cos a - 1) - (Real.sin a - a)| := by congr 1; ring
    _ ≤ |a * (Real.cos a - 1)| + |Real.sin a - a| := abs_sub _ _
    _ = a * |Real.cos a - 1| + |Real.sin a - a| := by
      rw [abs_mul, abs_of_nonneg ha]
    _ ≤ a * (a^2/2) + a^3/4 :=
      add_le_add (mul_le_mul_of_nonneg_left (cos_linear_remainder a) ha)
        (sin_linear_remainder a ha hasmall)
    _ ≤ a^3 := by nlinarith [pow_nonneg ha 3]

/-- Unscaled denominator-times-target minus numerator-times-source. -/
def scalarFactorResidual (h a x : ℝ) : ℂ :=
  (1 + Complex.I * (a : ℂ) * (spatialSymbol h : ℂ)) * phase (x-2*a) -
  (1 - Complex.I * (a : ℂ) * (spatialSymbol h : ℂ)) * phase x

theorem scalarFactorResidual_midpoint (h a x : ℝ) :
    scalarFactorResidual h a x = phase (x-a) * (2 * Complex.I) *
      ((a * spatialSymbol h * Real.cos a - Real.sin a : ℝ) : ℂ) := by
  have hminus : phase (x-2*a) = phase (x-a) * phase (-a) := by
    rw [← phase_add]; congr 1; ring
  have hplus : phase x = phase (x-a) * phase a := by
    rw [← phase_add]; congr 1; ring
  unfold scalarFactorResidual
  rw [hminus, hplus, phase_formula (-a), phase_formula a]
  simp only [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem scalarFactorResidual_bound (h a x : ℝ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    ‖scalarFactorResidual h a x‖ ≤ 2*a^3 + a*h^2/4 := by
  have hs := spatialSymbol_consistency h hh hhsmall
  have ht := midpoint_temporal_remainder a ha hasmall
  have hmid : |a * spatialSymbol h * Real.cos a - Real.sin a| ≤
      a * (h^2/8) + a^3 := by
    calc
      _ = |a * (spatialSymbol h - 1) * Real.cos a +
        (a * Real.cos a - Real.sin a)| := by congr 1; ring
      _ ≤ |a * (spatialSymbol h - 1) * Real.cos a| +
        |a * Real.cos a - Real.sin a| := abs_add_le _ _
      _ = a * |spatialSymbol h - 1| * |Real.cos a| +
        |a * Real.cos a - Real.sin a| := by rw [abs_mul, abs_mul, abs_of_nonneg ha]
      _ ≤ a * (h^2/8) * 1 + a^3 := by
        apply add_le_add _ ht
        exact mul_le_mul (mul_le_mul_of_nonneg_left hs ha) (Real.abs_cos_le_one a)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [scalarFactorResidual_midpoint, norm_mul, norm_mul, phase_norm]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  norm_num
  nlinarith

end NDEAEvolve.Exp006

-- SOURCE Exp005ModeBridge.lean SHA256 8c977973a96f05247a26cb5ff14e97dd2dcf90fb57f3ef14520cd2f84300fbdf

/-! Discharge Exp005's actual implicit-factor residual budget on a concrete
nonconstant periodic split-Schrodinger solution and the real cyclic stencil. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp006

def sampleState (n : ℕ) (h s : ℝ) : E (n+1) :=
  WithLp.toLp 2 (PeriodicGrid.sample h (fun x => phase (x-s)))

theorem shifted_phase_periodic (s : ℝ) :
    Function.Periodic (fun x => phase (x-s)) (2*Real.pi) := by
  intro x
  change phase (x+2*Real.pi-s) = phase (x-s)
  rw [show x+2*Real.pi-s = (x-s)+2*Real.pi by ring]
  exact phase_periodic (x-s)

theorem sampled_laplacian_eigen (n : ℕ) (h s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi) (i : Fin (n+1)) :
    (PeriodicGrid.laplacian n h).mulVec (WithLp.ofLp (sampleState n h s)) i =
      (spatialSymbol h : ℂ) * phase ((i.val : ℝ)*h-s) := by
  change (PeriodicGrid.laplacian n h).mulVec
    (PeriodicGrid.sample h (fun x => phase (x-s))) i = _
  rw [PeriodicGrid.matrix_sample_stencil (2*Real.pi) h _
    (shifted_phase_periodic s) hmesh]
  rw [show (i.val : ℝ)*h+h-s = ((i.val : ℝ)*h-s)+h by ring,
    show (i.val : ℝ)*h-h-s = ((i.val : ℝ)*h-s)-h by ring]
  exact phase_centeredStencil h ((i.val : ℝ)*h-s)

theorem factorResidual_component {n : ℕ} (H : Mat n) (a : ℝ)
    (u v : E n) (i : Fin n) :
    WithLp.ofLp (factorResidual H a u v) i =
      (WithLp.ofLp v i + Complex.I*(a : ℂ)*(H.mulVec (WithLp.ofLp v) i)) -
      (WithLp.ofLp u i - Complex.I*(a : ℂ)*(H.mulVec (WithLp.ofLp u) i)) := by
  change (cayleyD a H).mulVec (WithLp.ofLp v) i -
    (cayleyN a H).mulVec (WithLp.ofLp u) i = _
  simp [cayleyD, cayleyN, skewPart, cscalar, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec]

theorem actual_factorResidual_component (n : ℕ) (h a s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi) (i : Fin (n+1)) :
    WithLp.ofLp (factorResidual (PeriodicGrid.laplacian n h) a
      (sampleState n h s) (sampleState n h (s+2*a))) i =
      scalarFactorResidual h a ((i.val : ℝ)*h-s) := by
  rw [factorResidual_component, sampled_laplacian_eigen n h (s+2*a) hmesh,
    sampled_laplacian_eigen n h s hmesh]
  change (phase ((i.val : ℝ)*h-(s+2*a)) + _ ) -
    (phase ((i.val : ℝ)*h-s) - _) = _
  rw [show (i.val : ℝ)*h-(s+2*a) = ((i.val : ℝ)*h-s)-2*a by ring]
  unfold scalarFactorResidual
  ring

theorem actual_factorResidual_weighted_bound (n : ℕ) (h a s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    weightedNorm h (factorResidual (PeriodicGrid.laplacian n h) a
      (sampleState n h s) (sampleState n h (s+2*a))) ≤
      Real.sqrt (2*Real.pi) * (2*a^3+a*h^2/4) := by
  let r := factorResidual (PeriodicGrid.laplacian n h) a
    (sampleState n h s) (sampleState n h (s+2*a))
  have hb := weightedNorm_of_pointwise_bound h (2*Real.pi) (2*a^3+a*h^2/4)
    hh.le (by positivity) hmesh (WithLp.ofLp r) (by positivity)
    (fun i => by
      dsimp [r]
      rw [actual_factorResidual_component n h a s hmesh]
      exact scalarFactorResidual_bound h a _ hh hhsmall ha hasmall)
  simpa only [WithLp.toLp_ofLp] using hb

/-- The exact Exp005 budget premise, now derived for concrete cyclic matrices.
No residual, regularity, or generator-norm hypothesis is supplied. -/
theorem actual_stageResidualBudget_bound (n : ℕ) (h k s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 2) :
    stageResidualBudget h k (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h)
      (sampleState n h s) (sampleState n h (s+k/2))
      (sampleState n h (s+3*k/2)) (sampleState n h (s+2*k)) ≤
      k * (((5/16 : ℝ)*Real.sqrt (2*Real.pi))*k^2 +
        ((1/4 : ℝ)*Real.sqrt (2*Real.pi))*h^2) := by
  have h1 := actual_factorResidual_weighted_bound n h (k/4) s hmesh hh hhsmall
    (by positivity) (by linarith)
  have h2 := actual_factorResidual_weighted_bound n h (k/2) (s+k/2) hmesh hh hhsmall
    (by positivity) (by linarith)
  have h3 := actual_factorResidual_weighted_bound n h (k/4) (s+3*k/2) hmesh hh hhsmall
    (by positivity) (by linarith)
  rw [show s+2*(k/4)=s+k/2 by ring] at h1
  rw [show s+k/2+2*(k/2)=s+3*k/2 by ring] at h2
  rw [show s+3*k/2+2*(k/4)=s+2*k by ring] at h3
  unfold stageResidualBudget
  calc
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The physical reference trajectory is exactly samples of U(j*k,x). -/
def reference (n : ℕ) (h k : ℝ) (j : ℕ) : E (n+1) :=
  sampleState n h (2*(j : ℝ)*k)

theorem reference_is_sampled_mode (n : ℕ) (h k : ℝ) (j : ℕ) (i : Fin (n+1)) :
    WithLp.ofLp (reference n h k j) i = mode ((j : ℝ)*k) ((i.val : ℝ)*h) := by
  change phase ((i.val : ℝ)*h-(2*(j : ℝ)*k)) =
    phase ((i.val : ℝ)*h-2*((j : ℝ)*k))
  congr 1
  ring

/-- Exp005's fixed-time theorem specialized with its formerly assumed budget
discharged. Constants are uniform over all admissible finite periodic meshes. -/
theorem concrete_periodic_fixed_time_error (n : ℕ) (h k T : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 2)
    (v : ℕ → E (n+1))
    (hv : ∀ j, v (j+1) = symmetricStepHat
      (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h) k (v j))
    (N : ℕ) (horizon : (N : ℝ)*k ≤ T) :
    weightedNorm h (reference n h k N-v N) ≤
      weightedNorm h (reference n h k 0-v 0) +
      T*(((5/16 : ℝ)*Real.sqrt (2*Real.pi))*k^2 +
        ((1/4 : ℝ)*Real.sqrt (2*Real.pi))*h^2) := by
  apply symmetric_stage_residual_fixed_time_error h k T
    ((5/16 : ℝ)*Real.sqrt (2*Real.pi)) ((1/4 : ℝ)*Real.sqrt (2*Real.pi))
    (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h)
    (PeriodicGrid.isHermitian n h) (PeriodicGrid.isHermitian n h)
    (reference n h k) v
    (fun j => sampleState n h (2*(j : ℝ)*k+k/2))
    (fun j => sampleState n h (2*(j : ℝ)*k+3*k/2))
    hv N hk (by positivity) (by positivity) horizon
  intro j _hj
  have hb := actual_stageResidualBudget_bound n h k (2*(j : ℝ)*k)
    hmesh hh hhsmall hk hksmall
  have hnext : 2*((j+1 : ℕ) : ℝ)*k = 2*(j : ℝ)*k+2*k := by push_cast; ring
  simpa only [reference, hnext] using hb

/-- Across varying physical grids the scalar weighted error tends to zero.
Terminal times satisfy N_q*k_q≤T; no equality to T is silently imposed. -/
theorem concrete_periodic_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (hmesh : ∀ q, ((n q+1 : ℕ) : ℝ)*h q = 2*Real.pi)
    (hh : ∀ q, 0 < h q) (hhsmall : ∀ q, h q ≤ 1)
    (hk : ∀ q, 0 ≤ k q) (hksmall : ∀ q, k q ≤ 2)
    (v : (q : ℕ) → ℕ → E (n q+1))
    (hv : ∀ q j, v q (j+1) = symmetricStepHat
      (PeriodicGrid.laplacian (n q) (h q)) (PeriodicGrid.laplacian (n q) (h q))
        (k q) (v q j))
    (horizon : ∀ q, (N q : ℝ)*k q ≤ T)
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hinitial : Filter.Tendsto
      (fun q => weightedNorm (h q) (reference (n q) (h q) (k q) 0-v q 0))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun q => weightedNorm (h q) (reference (n q) (h q) (k q) (N q)-v q (N q)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => weightedNorm_nonneg (h q) _)
  · intro q
    exact concrete_periodic_fixed_time_error (n q) (h q) (k q) T
      (hmesh q) (hh q) (hhsmall q) (hk q) (hksmall q) (v q) (hv q)
      (N q) (horizon q)
  · exact mesh_error_majorant_tendsto_zero k h _ T
      ((5/16 : ℝ)*Real.sqrt (2*Real.pi)) ((1/4 : ℝ)*Real.sqrt (2*Real.pi))
      hk_limit hh_limit hinitial

end NDEAEvolve.Exp006

-- SOURCE Controls.lean SHA256 6396f20d903db0a8c04f36c529f7209fcd6be693abfbc417d1dc081ee4f714e7

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp006.Controls

/-- A concrete admissible grid/time witness; the production hypotheses are satisfiable. -/
theorem admissible_eight_point_grid :
    (0 : ℝ) < Real.pi/4 ∧ Real.pi/4 ≤ 1 ∧
    ((7+1 : ℕ) : ℝ)*(Real.pi/4) = 2*Real.pi ∧
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 2 := by
  constructor
  · positivity
  constructor
  · linarith [Real.pi_le_four]
  constructor
  · norm_num <;> ring
  norm_num

/-- The excluded zero mesh falsifies the spatial consistency statement. -/
theorem zero_mesh_consistency_false :
    ¬ |spatialSymbol 0 - 1| ≤ (0 : ℝ)^2/8 := by
  norm_num [spatialSymbol]

/-- The discrete first mode has a strictly nonzero spatial defect. -/
theorem spatial_error_is_present (h : ℝ) (hh : 0 < h) : spatialSymbol h ≠ 1 :=
  ne_of_lt (spatialSymbol_strictly_below_continuum h hh.ne')

/-- The first Fourier mode is not the constant zero solution. -/
theorem solution_nonconstant_and_nonzero (t : ℝ) :
    (∃ x y, mode t x ≠ mode t y) ∧ (∀ x, mode t x ≠ 0) :=
  ⟨mode_nonconstant t, mode_nonzero t⟩

/-- Both equal split Laplacians act nontrivially on this solution. -/
theorem both_continuous_generators_active (t x : ℝ) :
    -deriv (deriv (mode t)) x = mode t x ∧
    -deriv (deriv (mode t)) x ≠ 0 := by
  have hsecond : deriv (deriv (mode t)) x = - mode t x := by
    simpa using! mode_second_derivative t x
  rw [hsecond]
  simpa using mode_nonzero t x

/-- Exact zero time-step control on the measured scalar factors. -/
theorem zero_step_residual (h x : ℝ) : scalarFactorResidual h 0 x = 0 := by
  simp [scalarFactorResidual]

end NDEAEvolve.Exp006.Controls



-- SOURCE lean/ReducedNoncommuting.lean SHA256 56d1fcea52c27dafbb18c411749a5cf8545fe317ca3dbdd7a840e74d507d052c

/-! A noncommuting two-component Fourier reduction and a mesh-uniform
complete-step consistency estimate. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007

def Z : Mat 2 := ![![1, 0], ![0, -1]]
def X : Mat 2 := ![![0, 1], ![1, 0]]
def A (lambda : ℝ) : Mat 2 := (lambda : ℂ) • 1 + Z
abbrev A0 : Mat 2 := A 1
abbrev B : Mat 2 := X

theorem Z_isHermitian : Z.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Z, Matrix.conjTranspose_apply]

theorem X_isHermitian : X.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.conjTranspose_apply]

theorem A_isHermitian (lambda : ℝ) : (A lambda).IsHermitian := by
  unfold A Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
    Z_isHermitian.eq]

theorem B_isHermitian : B.IsHermitian := X_isHermitian

theorem A_noncommutes_B (lambda : ℝ) : ¬ Commute (A lambda) B := by
  intro hc
  have he := congrArg (fun M : Mat 2 => M 0 1) hc.eq
  norm_num [A, B, X, Z, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply] at he

private theorem Z_unitary : IsUnitary Z := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply]

private theorem X_unitary : IsUnitary X := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply]

theorem unitary_opNorm_le_one {n : ℕ} (M : Mat n) (hM : IsUnitary M) :
    ‖operatorOf M‖ ≤ 1 := by
  calc
    _ = ‖(1 : E n →L[ℂ] E n)‖ := by
      simpa only [mul_one] using
        CStarRing.norm_mem_unitary_mul (1 : E n →L[ℂ] E n)
          (unitary_toEuclideanCLM hM)
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

theorem Z_opNorm_le_one : ‖operatorOf Z‖ ≤ 1 :=
  unitary_opNorm_le_one Z Z_unitary

theorem B_opNorm_le_one : ‖operatorOf B‖ ≤ 1 :=
  unitary_opNorm_le_one X X_unitary

theorem A_opNorm_le_two (lambda : ℝ) (hl : 0 ≤ lambda) (hu : lambda ≤ 1) :
    ‖operatorOf (A lambda)‖ ≤ 2 := by
  have hid : ‖(1 : E 2 →L[ℂ] E 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hz := Z_opNorm_le_one
  simp only [A, operatorOf, map_add, map_smul, map_one]
  calc
    _ ≤ ‖(lambda : ℂ) • (1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := norm_add_le _ _
    _ = lambda * ‖(1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    _ ≤ lambda * 1 + 1 := add_le_add (mul_le_mul_of_nonneg_left hid hl) hz
    _ ≤ 2 := by linarith

theorem spatialSymbol_nonneg (h : ℝ) : 0 ≤ Exp006.spatialSymbol h := by
  unfold Exp006.spatialSymbol
  exact div_nonneg (by linarith [Real.cos_le_one h]) (sq_nonneg h)

theorem spatialSymbol_le_one (h : ℝ) (hh : h ≠ 0) :
    Exp006.spatialSymbol h ≤ 1 :=
  (Exp006.spatialSymbol_strictly_below_continuum h hh).le

theorem A_difference_norm_le (lambda mu : ℝ) :
    ‖operatorOf (A lambda - A mu)‖ ≤ |lambda-mu| := by
  have he : A lambda - A mu = ((lambda-mu : ℝ) : ℂ) • (1 : Mat 2) := by
    unfold A
    push_cast
    module
  rw [he]
  simp only [operatorOf, map_smul, map_one, norm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E 2))
    (abs_nonneg (lambda-mu))).trans_eq (mul_one _)

theorem Chat_affine {n : ℕ} (a : ℝ) (P : Mat n) (hP : P.IsHermitian) :
    Chat P a = Rhat P a + Rhat P a - 1 := by
  have hm : cayley a P = cayleyR a P + cayleyR a P - 1 := by
    simpa only [cayley, cayleyN, two_mul] using
      cayley_affine_of_right_inverse (skewPart a P) (cayleyR a P)
        (cayleyD_mul_cayleyR a P hP)
  simpa only [Chat, Rhat, map_add, map_sub, map_one] using
    congrArg (fun M : Mat n => operatorOf M) hm

theorem resolvent_perturbation_identity {n : ℕ} (a : ℝ) (P Q : Mat n)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    Rhat P a - Rhat Q a =
      Rhat P a * (denominatorHat Q a - denominatorHat P a) * Rhat Q a := by
  have hp := resolvent_mul_denominatorHat a P hP
  have hq : denominatorHat Q a * Rhat Q a = 1 := by
    simpa only [denominatorHat, Rhat, operatorOf, map_mul, map_one] using
      congrArg (fun M : Mat n => operatorOf M) (cayleyD_mul_cayleyR a Q hQ)
  calc
    _ = Rhat P a * (denominatorHat Q a * Rhat Q a) -
        (Rhat P a * denominatorHat P a) * Rhat Q a := by rw [hp, hq]; simp
    _ = _ := by simp only [mul_sub, sub_mul, mul_assoc]

private theorem norm_mul_bound {R : Type*} [NormedRing R]
    {P Q : R} {p q : ℝ} (hp : ‖P‖ ≤ p) (hq : ‖Q‖ ≤ q) :
    ‖P*Q‖ ≤ p*q :=
  (norm_mul_le P Q).trans
    (mul_le_mul hp hq (norm_nonneg Q) ((norm_nonneg P).trans hp))

theorem cayley_perturbation_opNorm_le {n : ℕ} (a : ℝ) (P Q : Mat n)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ‖Chat P a - Chat Q a‖ ≤ 2*|a| *‖operatorOf (P-Q)‖ := by
  have hd : denominatorHat Q a - denominatorHat P a =
      (Complex.I*(a : ℂ)) • operatorOf (Q-P) := by
    simp only [denominatorHat, cayleyD, skewPart, cscalar, operatorOf,
      map_add, map_smul, map_one, map_sub, smul_sub]
    abel
  have hn : ‖denominatorHat Q a - denominatorHat P a‖ =
      |a| *‖operatorOf (P-Q)‖ := by
    rw [hd, norm_smul]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, operatorOf, map_sub]
    rw [norm_sub_rev]
  have hr : ‖Rhat P a - Rhat Q a‖ ≤ |a| *‖operatorOf (P-Q)‖ := by
    rw [resolvent_perturbation_identity a P Q hP hQ]
    calc
      _ ≤ (1*‖denominatorHat Q a-denominatorHat P a‖)*1 :=
        norm_mul_bound
          (norm_mul_bound (cayleyR_toEuclideanCLM_opNorm_le_one a P hP) (le_refl _))
          (cayleyR_toEuclideanCLM_opNorm_le_one a Q hQ)
      _ = _ := by rw [hn]; ring
  have hc : Chat P a - Chat Q a =
      (Rhat P a-Rhat Q a)+(Rhat P a-Rhat Q a) := by
    rw [Chat_affine a P hP, Chat_affine a Q hQ]
    abel
  rw [hc]
  exact (norm_add_le _ _).trans (by linarith)

theorem cayley_opNorm_le_one {n : ℕ} (a : ℝ) (P : Mat n)
    (hP : P.IsHermitian) : ‖Chat P a‖ ≤ 1 :=
  unitary_opNorm_le_one (cayley a P) (cayley_unitary a P hP)

theorem symmetric_perturbation_opNorm_le (lambda mu k : ℝ) :
    ‖symmetricStepHat (A lambda) B k - symmetricStepHat (A mu) B k‖ ≤
      |k| *|lambda-mu| := by
  let S := Chat (A lambda) (k/4)
  let R := Chat (A mu) (k/4)
  let V := Chat B (k/2)
  have hs : ‖S‖ ≤ 1 := cayley_opNorm_le_one _ _ (A_isHermitian lambda)
  have hr : ‖R‖ ≤ 1 := cayley_opNorm_le_one _ _ (A_isHermitian mu)
  have hv : ‖V‖ ≤ 1 := cayley_opNorm_le_one _ _ B_isHermitian
  have hd : ‖S-R‖ ≤ |k| /2*|lambda-mu| := by
    calc
      _ ≤ 2*|k/4| *‖operatorOf (A lambda-A mu)‖ :=
        cayley_perturbation_opNorm_le _ _ _ (A_isHermitian lambda) (A_isHermitian mu)
      _ ≤ 2*|k/4| *|lambda-mu| :=
        mul_le_mul_of_nonneg_left (A_difference_norm_le lambda mu) (by positivity)
      _ = _ := by
        rw [abs_div, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
        ring
  have he : S*V*S-R*V*R = (S-R)*V*S+R*V*(S-R) := by
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  change ‖S*V*S-R*V*R‖ ≤ _
  rw [he]
  have h1 := norm_mul_bound (norm_mul_bound hd hv) hs
  have h2 := norm_mul_bound (norm_mul_bound hr hv) hd
  exact (norm_add_le _ _).trans (by linarith)

theorem reduced_local_error (h k : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1)
    (hk : 0 ≤ k) (hksmall : k ≤ 1/6) :
    ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k -
      exactStepHat (A0+B) (k/2)‖ ≤ k*(27000*k^2+h^2/8) := by
  have ha := A_opNorm_le_two 1 (by norm_num) (by norm_num)
  have hb := B_opNorm_le_one
  have hsum : ‖operatorOf A0‖+‖operatorOf B‖ ≤ 3 := by linarith
  have hstep : 2*|k| *(‖operatorOf A0‖+‖operatorOf B‖) ≤ 1 := by
    rw [abs_of_nonneg hk]
    have hp := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*k by positivity)
    linarith
  have ht := symmetric_cayley_exp_local_opNorm_le k A0 B
    (A_isHermitian 1) B_isHermitian hstep
  have hcube : (‖operatorOf A0‖+‖operatorOf B‖)^3 ≤ 27 := by
    calc
      _ ≤ (3:ℝ)^3 := by gcongr
      _ = 27 := by norm_num
  have htemp : ‖symmetricStepHat A0 B k-exactStepHat (A0+B) (k/2)‖ ≤
      27000*k^3 := by
    rw [abs_of_nonneg hk] at ht
    have hp := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 1000*k^3 by positivity)
    exact ht.trans (by nlinarith)
  have hspace : ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k-
      symmetricStepHat A0 B k‖ ≤ k*h^2/8 := by
    have hp := symmetric_perturbation_opNorm_le (Exp006.spatialSymbol h) 1 k
    rw [abs_of_nonneg hk] at hp
    have hc := mul_le_mul_of_nonneg_left
      (Exp006.spatialSymbol_consistency h hh hhsmall) hk
    exact hp.trans (by nlinarith)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat (A (Exp006.spatialSymbol h)) B k)
    (symmetricStepHat A0 B k) (exactStepHat (A0+B) (k/2))
  nlinarith

end NDEAEvolve.Exp007


-- SOURCE lean/SpinorGrid.lean SHA256 a9f9f181472cfe1edc9774156fa8cbd8e801549a35471480cabff75171185d1f

/-! Full periodic spinor grid and its invariant first Fourier mode. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp006

namespace NDEAEvolve.Exp007.SpinorGrid

section GenericCayley
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vec (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev op (H : Matrix ι ι ℂ) : Vec ι →L[ℂ] Vec ι :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) H
def den (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 + (Complex.I * (a : ℂ)) • H
def num (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 - (Complex.I * (a : ℂ)) • H
def resolvent (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := (den a H)⁻¹
def cayleyMatrix (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := num a H * resolvent a H
abbrev step (a : ℝ) (H : Matrix ι ι ℂ) := op (cayleyMatrix a H)

theorem den_star (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    star (den a H) = num a H := by
  have hs : star H = H := hH.eq
  simp [den, num, star_smul, hs, sub_eq_add_neg]

theorem den_isUnit (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    IsUnit (den a H) := by
  have hs : star ((Complex.I * (a : ℂ)) • H) = -((Complex.I * (a : ℂ)) • H) := by
    have hstar : star H = H := hH.eq
    simp [star_smul, hstar]
  have hg : star (den a H) * den a H =
      1 + star ((Complex.I * (a : ℂ)) • H) * ((Complex.I * (a : ℂ)) • H) := by
    rw [den_star a H hH, hs]
    unfold num den
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  have hp : Matrix.PosDef (star (den a H) * den a H) := by
    rw [hg]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self _)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply hi
  simpa only [Matrix.mulVec_mulVec] using
    congrArg (fun z => (star (den a H)).mulVec z) hxy

theorem den_mul_resolvent (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    den a H * resolvent a H = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (den_isUnit a H hH))

theorem resolvent_mul_den (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    resolvent a H * den a H = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (den_isUnit a H hH))

theorem den_step (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    den a H * cayleyMatrix a H = num a H := by
  have hc : den a H * num a H = num a H * den a H := by
    unfold den num
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  rw [cayleyMatrix, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, den_mul_resolvent a H hH,
    Matrix.mul_one]

/-- Each full-grid Crank--Nicolson stage has exactly one solution. -/
theorem stage_unique (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (u v : Vec ι) :
    op (den a H) v = op (num a H) u ↔ v = step a H u := by
  have hi : Function.Injective (op (den a H)) := by
    intro x y hxy
    have hp := congrArg (op (resolvent a H)) hxy
    have hid : op (resolvent a H) * op (den a H) = 1 := by
      rw [← map_mul, resolvent_mul_den a H hH, map_one]
    simpa only [← ContinuousLinearMap.mul_apply, hid, ContinuousLinearMap.one_apply] using hp
  have heq : op (den a H) (step a H u) = op (num a H) u := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, den_step a H hH]
  exact ⟨fun h => hi (h.trans heq.symm), fun h => h ▸ heq⟩

end GenericCayley

theorem den_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    op (den a H) (J v) = J (op (den a K) v) := by
  simp only [den, map_add, map_one, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, hJK]

theorem num_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    op (num a H) (J v) = J (op (num a K) v) := by
  simp only [num, map_sub, map_one, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, hJK]

/-- A generator intertwiner also intertwines the actual inverse Cayley factors. -/
theorem step_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    step a H (J v) = J (step a K v) := by
  have hd := den_intertwines J H K hJK a
  have hn := num_intertwines J H K hJK a
  apply ((stage_unique a H hH (J v) (J (step a K v))).mp ?_).symm
  rw [hd, hn]
  exact congrArg J ((stage_unique a K hK v (step a K v)).mpr rfl)

abbrev Grid (n : ℕ) := Fin (n + 1) × Fin 2

def lift (n : ℕ) (h : ℝ) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => phase ((p.1.val : ℝ) * h) * v p.2)

def liftLinear (n : ℕ) (h : ℝ) : E 2 →ₗ[ℂ] Vec (Grid n) where
  toFun := lift n h
  map_add' := by
    intro u v
    ext p
    change phase _ * (u p.2 + v p.2) = phase _ * u p.2 + phase _ * v p.2
    ring
  map_smul' := by
    intro c v
    ext p
    change phase _ * (c * v p.2) = c * (phase _ * v p.2)
    ring

def liftCLM (n : ℕ) (h : ℝ) : E 2 →L[ℂ] Vec (Grid n) :=
  (liftLinear n h).toContinuousLinearMap

@[simp] theorem liftCLM_apply (n : ℕ) (h : ℝ) (v : E 2) : liftCLM n h v = lift n h v := rfl

theorem lift_norm_sq (n : ℕ) (h : ℝ) (v : E 2) :
    ‖lift n h v‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [lift, Fintype.sum_prod_type, norm_mul]
  ring

theorem lift_weighted_norm (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    Real.sqrt h * ‖lift n h v‖ = Real.sqrt (2 * Real.pi) * ‖v‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), lift_norm_sq]
  nlinarith [hmesh]


theorem step_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    step a H ∈ unitary (Vec ι →L[ℂ] Vec ι) := by
  have hn : den a H * star (den a H) = star (den a H) * den a H := by
    rw [den_star a H hH]
    unfold den num
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  have hu := unitary_of_normal_and_inverse (den a H) (resolvent a H) hn
    (den_mul_resolvent a H hH) (resolvent_mul_den a H hH)
  rw [den_star a H hH] at hu
  change cayleyMatrix a H * star (cayleyMatrix a H) = 1 ∧
    star (cayleyMatrix a H) * cayleyMatrix a H = 1 at hu
  rw [Unitary.mem_iff]
  constructor
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M) hu.2
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M) hu.1

def potential (n : ℕ) (K : Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  (1 : Mat (n + 1)) ⊗ₖ K

def hamiltonian (n : ℕ) (h : ℝ) (K : Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2) + potential n K

theorem potential_isHermitian (n : ℕ) (K : Mat 2) (hK : K.IsHermitian) :
    (potential n K).IsHermitian := by
  unfold potential Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hK.eq]

theorem hamiltonian_isHermitian (n : ℕ) (h : ℝ) (K : Mat 2) (hK : K.IsHermitian) :
    (hamiltonian n h K).IsHermitian := by
  unfold hamiltonian
  apply Matrix.IsHermitian.add _ (potential_isHermitian n K hK)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (PeriodicGrid.isHermitian n h).eq]

theorem potential_apply (n : ℕ) (K : Mat 2) (u : Vec (Grid n))
    (i : Fin (n + 1)) (a : Fin 2) :
    op (potential n K) u (i,a) = ∑ b : Fin 2, K a b * u (i,b) := by
  change (potential n K).mulVec (WithLp.ofLp u) (i,a) = _
  simp [potential, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

theorem laplacian_apply (n : ℕ) (h : ℝ) (u : Vec (Grid n))
    (i : Fin (n + 1)) (a : Fin 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) u (i,a) =
      (PeriodicGrid.laplacian n h).mulVec (fun j => u (j,a)) i := by
  change (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)).mulVec (WithLp.ofLp u) (i,a) = _
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

theorem potential_intertwines (n : ℕ) (h : ℝ) (K : Mat 2) (v : E 2) :
    op (potential n K) (liftCLM n h v) = liftCLM n h (operatorOf K v) := by
  ext p
  rcases p with ⟨i,a⟩
  rw [potential_apply]
  change (∑ b : Fin 2, K a b * (phase ((i.val : ℝ)*h) * v b)) =
    phase ((i.val : ℝ)*h) * (K.mulVec (WithLp.ofLp v) a)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem laplacian_lift (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) (liftCLM n h v) =
      (spatialSymbol h : ℂ) • liftCLM n h v := by
  ext p
  rcases p with ⟨i,a⟩
  rw [laplacian_apply]
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((j.val : ℝ)*h) * v a) i =
      (spatialSymbol h : ℂ) * (phase ((i.val : ℝ)*h) * v a)
  have hf : Function.Periodic (fun x => phase x * v a) (2*Real.pi) := by
    intro x
    change phase (x + 2 * Real.pi) * v a = phase x * v a
    rw [phase_periodic x]
  have hs := PeriodicGrid.matrix_sample_stencil (n := n) (2*Real.pi) h
    (fun x => phase x * v a) hf hmesh i
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((j.val : ℝ)*h) * v a) i = _ at hs
  rw [hs]
  have hc := phase_centeredStencil h ((i.val : ℝ)*h)
  unfold centeredStencil at hc
  calc
    _ = ((2*phase ((i.val : ℝ)*h) - phase ((i.val : ℝ)*h+h) -
      phase ((i.val : ℝ)*h-h))/(h : ℂ)^2) * v a := by ring
    _ = _ := by rw [hc]; ring

theorem hamiltonian_intertwines (n : ℕ) (h : ℝ) (K : Mat 2)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (hamiltonian n h K) (liftCLM n h v) =
      liftCLM n h (operatorOf ((spatialSymbol h : ℂ) • 1 + K) v) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, laplacian_lift n h hmesh,
    potential_intertwines, operatorOf, map_smul, map_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]

theorem scalar_add_isHermitian (lambda : ℝ) (K : Mat 2) (hK : K.IsHermitian) :
    ((lambda : ℂ) • (1 : Mat 2) + K).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hK.eq]

theorem hamiltonian_step_lift (n : ℕ) (h a : ℝ) (K : Mat 2) (hK : K.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    step a (hamiltonian n h K) (liftCLM n h v) =
      liftCLM n h (Chat ((spatialSymbol h : ℂ) • 1 + K) a v) := by
  exact step_intertwines (liftCLM n h) (hamiltonian n h K) _
    (hamiltonian_isHermitian n h K hK) (scalar_add_isHermitian _ K hK)
    (hamiltonian_intertwines n h K hmesh) a v

theorem potential_step_lift (n : ℕ) (h a : ℝ) (K : Mat 2) (hK : K.IsHermitian)
    (v : E 2) :
    step a (potential n K) (liftCLM n h v) = liftCLM n h (Chat K a v) := by
  exact step_intertwines (liftCLM n h) (potential n K) K
    (potential_isHermitian n K hK) hK (potential_intertwines n h K) a v

def symmetric (n : ℕ) (h k : ℝ) (K Q : Mat 2) : Vec (Grid n) →L[ℂ] Vec (Grid n) :=
  step (k / 4) (hamiltonian n h K) * step (k / 2) (potential n Q) *
    step (k / 4) (hamiltonian n h K)

theorem symmetric_mem_unitary (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) :
    symmetric n h k K Q ∈ unitary (Vec (Grid n) →L[ℂ] Vec (Grid n)) := by
  exact (unitary _).mul_mem ((unitary _).mul_mem
    (step_mem_unitary _ _ (hamiltonian_isHermitian n h K hK))
    (step_mem_unitary _ _ (potential_isHermitian n Q hQ)))
    (step_mem_unitary _ _ (hamiltonian_isHermitian n h K hK))

theorem symmetric_pow_norm (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) (N : ℕ) (u : Vec (Grid n)) :
    ‖(symmetric n h k K Q ^ N) u‖ = ‖u‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    ((unitary _).pow_mem (symmetric_mem_unitary n h k K Q hK hQ) N) u

theorem symmetric_lift (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    symmetric n h k K Q (liftCLM n h v) =
      liftCLM n h (symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k v) := by
  simp only [symmetric, symmetricStepHat, ContinuousLinearMap.mul_apply,
    hamiltonian_step_lift n h _ K hK hmesh, potential_step_lift n h _ Q hQ]

theorem symmetric_pow_lift (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (v : E 2) :
    (symmetric n h k K Q ^ N) (liftCLM n h v) =
      liftCLM n h ((symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k ^ N) v) := by
  induction N generalizing v with
  | zero => simp
  | succ N ih =>
    simp only [pow_succ, ContinuousLinearMap.mul_apply,
      symmetric_lift n h k K Q hK hQ hmesh, ih]

/-- Exact conversion of full-grid error into the bounded two-component error. -/
theorem symmetric_pow_weighted_error (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (u v : E 2) :
    Real.sqrt h * ‖(symmetric n h k K Q ^ N) (liftCLM n h u) - liftCLM n h v‖ =
      Real.sqrt (2*Real.pi) *
        ‖(symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k ^ N) u - v‖ := by
  rw [symmetric_pow_lift n h k K Q hK hQ hmesh, ← map_sub]
  exact lift_weighted_norm n h hh hmesh _

theorem hamiltonian_apply_stencil (n : ℕ) (h : ℝ) (K : Mat 2)
    (u : Vec (Grid n)) (i : Fin (n + 1)) (a : Fin 2) :
    op (hamiltonian n h K) u (i,a) =
      (2*u (i,a) - u (PeriodicGrid.next i,a) - u (PeriodicGrid.prev i,a))/(h : ℂ)^2 +
        ∑ b : Fin 2, K a b * u (i,b) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, PiLp.add_apply,
    laplacian_apply, potential_apply, PeriodicGrid.laplacian_mulVec]

theorem hamiltonian_mul_potential (n : ℕ) (h : ℝ) (K Q : Mat 2) :
    hamiltonian n h K * potential n Q =
      PeriodicGrid.laplacian n h ⊗ₖ Q + potential n (K * Q) := by
  simp [hamiltonian, potential, Matrix.add_mul, ← Matrix.mul_kronecker_mul]

theorem potential_mul_hamiltonian (n : ℕ) (h : ℝ) (K Q : Mat 2) :
    potential n Q * hamiltonian n h K =
      PeriodicGrid.laplacian n h ⊗ₖ Q + potential n (Q * K) := by
  simp [hamiltonian, potential, Matrix.mul_add, ← Matrix.mul_kronecker_mul]

/-- Noncommuting internal components remain noncommuting on every full grid. -/
theorem hamiltonian_noncommutes_potential (n : ℕ) (h : ℝ) (K Q : Mat 2)
    (hKQ : ¬ Commute K Q) : ¬ Commute (hamiltonian n h K) (potential n Q) := by
  intro hc
  apply hKQ
  change K * Q = Q * K
  ext a b
  have he := congrArg (fun M : Matrix (Grid n) (Grid n) ℂ =>
    M ((0 : Fin (n + 1)),a) ((0 : Fin (n + 1)),b)) hc.eq
  rw [hamiltonian_mul_potential, potential_mul_hamiltonian] at he
  simp only [potential, Matrix.add_apply, Matrix.kronecker_apply,
    Matrix.one_apply_eq, one_mul] at he
  exact add_left_cancel he


end NDEAEvolve.Exp007.SpinorGrid


-- SOURCE lean/ContinuumSpinor.lean SHA256 925f1b96317f0e5a7587e40559679300befc747904e0c374f4d88b3b31202ed5

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp007

local instance (n : ℕ) : NormedAlgebra ℚ (E n →L[ℂ] E n) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E n →L[ℂ] E n)

def continuumPropagator {n : ℕ} (H : Mat n) (t : ℝ) : E n →L[ℂ] E n :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf H)

theorem continuumPropagator_eq_exactStepHat {n : ℕ} (H : Mat n) (t : ℝ) :
    continuumPropagator H t = exactStepHat H (t / 2) := by
  unfold continuumPropagator exactStepHat skewHat
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => NormedSpace.exp (z • operatorOf H))
  push_cast
  ring

theorem continuumPropagator_add {n : ℕ} (H : Mat n) (s t : ℝ) :
    continuumPropagator H (s + t) = continuumPropagator H s * continuumPropagator H t := by
  unfold continuumPropagator
  have hc : Commute ((-Complex.I * (s : ℂ)) • operatorOf H)
      ((-Complex.I * (t : ℂ)) • operatorOf H) :=
    by
      apply ContinuousLinearMap.ext
      intro w
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
      rw [smul_smul, smul_smul, mul_comm]
  rw [← NormedSpace.exp_add_of_commute hc]
  congr 1
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  push_cast
  module

theorem continuumEvolution_hasDerivAt {n : ℕ} (H : Mat n) (v0 : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => continuumPropagator H s v0)
      ((-Complex.I) • operatorOf H (continuumPropagator H t v0)) t := by
  let K : E n →L[ℂ] E n := (-Complex.I) • operatorOf H
  have hc := (hasDerivAt_exp_smul_const' K (t : ℂ)).clm_apply
    (hasDerivAt_const (t : ℂ) v0)
  have hr := hc.scomp t Complex.ofRealCLM.hasDerivAt
  simpa [K, continuumPropagator, smul_smul, mul_comm, Function.comp_def,
    ContinuousLinearMap.mul_apply] using! hr


/-- Arbitrary initial spinor evolved by the continuum Fourier-mode Hamiltonian. -/
def v (v0 : E 2) (t : ℝ) : E 2 := continuumPropagator (A0 + B) t v0

/-- A periodic spinor-valued continuum solution. -/
def U (v0 : E 2) (t x : ℝ) : E 2 := Exp006.phase x • v v0 t

@[simp] theorem v_initial (v0 : E 2) : v v0 0 = v0 := by
  have hz : (-Complex.I * (0 : ℂ)) • operatorOf (A0 + B) =
      (0 : E 2 →L[ℂ] E 2) := by
    apply ContinuousLinearMap.ext
    intro w
    change (-Complex.I * (0 : ℂ)) • (operatorOf (A0 + B) w) = 0
    simp
  change NormedSpace.exp ((-Complex.I * (0 : ℂ)) • operatorOf (A0 + B)) v0 = v0
  rw [hz, NormedSpace.exp_zero]
  rfl

@[simp] theorem U_initial (v0 : E 2) (x : ℝ) :
    U v0 0 x = Exp006.phase x • v0 := by simp [U]

theorem U_periodic (v0 : E 2) (t : ℝ) : Function.Periodic (U v0 t) (2 * Real.pi) := by
  intro x
  simp only [U, Exp006.phase_periodic x]

theorem v_hasDerivAt (v0 : E 2) (t : ℝ) :
    HasDerivAt (v v0) ((-Complex.I) • operatorOf (A0 + B) (v v0 t)) t :=
  continuumEvolution_hasDerivAt (A0 + B) v0 t

theorem U_time_hasDerivAt (v0 : E 2) (t x : ℝ) :
    HasDerivAt (fun s => U v0 s x)
      (Exp006.phase x • ((-Complex.I) • operatorOf (A0 + B) (v v0 t))) t := by
  exact (v_hasDerivAt v0 t).const_smul (Exp006.phase x)

theorem U_space_hasDerivAt (v0 : E 2) (t x : ℝ) :
    HasDerivAt (U v0 t) ((Exp006.phase x * Complex.I) • v v0 t) x := by
  exact (Exp006.phase_hasDerivAt x).smul_const (v v0 t)

theorem U_second_derivative (v0 : E 2) (t x : ℝ) :
    deriv (deriv (U v0 t)) x = - U v0 t x := by
  have hd : deriv (U v0 t) = fun y => (Exp006.phase y * Complex.I) • v v0 t :=
    funext fun y => (U_space_hasDerivAt v0 t y).deriv
  rw [hd, (((Exp006.phase_hasDerivAt x).mul_const Complex.I).smul_const (v v0 t)).deriv]
  simp [U, mul_assoc]

theorem v_norm (v0 : E 2) (t : ℝ) : ‖v v0 t‖ = ‖v0‖ := by
  unfold v
  rw [continuumPropagator_eq_exactStepHat]
  exact ContinuousLinearMap.norm_map_of_mem_unitary
    (exactStepHat_mem_unitary (t / 2) (A0 + B)
      ((A_isHermitian 1).add B_isHermitian)) v0

theorem U_norm (v0 : E 2) (t x : ℝ) : ‖U v0 t x‖ = ‖v0‖ := by
  simp [U, norm_smul, v_norm]

/-- The actual real derivatives solve the spinor Schrödinger PDE. -/
theorem U_schrodinger (v0 : E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => U v0 s x) t =
      -deriv (deriv (U v0 t)) x + operatorOf (Z + X) (U v0 t x) := by
  rw [(U_time_hasDerivAt v0 t x).deriv, U_second_derivative, neg_neg]
  have hi : Complex.I * (Exp006.phase x * (-Complex.I)) = Exp006.phase x := by
    calc
      _ = -(Complex.I * Complex.I) * Exp006.phase x := by ring
      _ = _ := by simp
  rw [smul_smul, smul_smul, mul_assoc, hi]
  have hH : A0 + B = 1 + (Z + X) := by simp [A0, A, B, add_assoc]
  rw [hH]
  simp [operatorOf, U, smul_add]

theorem v_exact_step (v0 : E 2) (t k : ℝ) :
    exactStepHat (A0 + B) (k / 2) (v v0 t) = v v0 (t + k) := by
  rw [← continuumPropagator_eq_exactStepHat]
  unfold v
  rw [add_comm t k, continuumPropagator_add, ContinuousLinearMap.mul_apply]

end NDEAEvolve.Exp007


-- SOURCE lean/ReducedClosure.lean SHA256 c859e1d430507defbe8439c4dd0d401aa11a2e00bb5cf4be2efd291b0515a7a0

/-! Explicit local stage residuals and finite-time reduced error. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007

theorem reduced_power_error (h k T : ℝ) (N : ℕ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) :
    ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k ^ N -
      exactStepHat (A0+B) (k/2) ^ N‖ ≤ T*(27000*k^2+h^2/8) := by
  have ht := unitary_pow_sub_pow_opNorm_le
    (symmetricStepHat (A (Exp006.spatialSymbol h)) B k)
    (exactStepHat (A0+B) (k/2)) N
    (symmetricStepHat_mem_unitary k _ _ (A_isHermitian _) B_isHermitian)
    (exactStepHat_mem_unitary (k/2) _ ((A_isHermitian 1).add B_isHermitian))
  calc
    _ ≤ (N : ℝ) * ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k -
        exactStepHat (A0+B) (k/2)‖ := ht
    _ ≤ (N : ℝ) * (k*(27000*k^2+h^2/8)) :=
      mul_le_mul_of_nonneg_left (reduced_local_error h k hh hhsmall hk hksmall)
        (Nat.cast_nonneg N)
    _ ≤ T*(27000*k^2+h^2/8) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right horizon (by positivity)

theorem reduced_power_error_apply (h k T : ℝ) (N : ℕ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (v : E 2) :
    ‖(symmetricStepHat (A (Exp006.spatialSymbol h)) B k ^ N) v -
      (exactStepHat (A0+B) (k/2) ^ N) v‖ ≤ T*(27000*k^2+h^2/8)*‖v‖ := by
  rw [← ContinuousLinearMap.sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (reduced_power_error h k T N hh hhsmall hk hksmall horizon) (norm_nonneg v))

theorem denominator_mul_cayley {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) : denominatorHat H a * Chat H a = numeratorHat H a := by
  have hc : cayleyD a H * cayleyN a H = cayleyN a H * cayleyD a H := by
    unfold cayleyD cayleyN
    noncomm_ring
  have he : cayleyD a H * cayley a H = cayleyN a H := by
    rw [cayley, ← mul_assoc, hc, mul_assoc, cayleyD_mul_cayleyR a H hH, mul_one]
  simpa only [denominatorHat, numeratorHat, Chat, operatorOf, map_mul] using
    congrArg (fun M : Mat n => operatorOf M) he

@[simp] theorem factorResidual_cayley_zero {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) (v : E n) :
    factorResidual H a v (Chat H a v) = 0 := by
  rw [factorResidual, ← ContinuousLinearMap.mul_apply, denominator_mul_cayley H a hH,
    sub_self]

theorem factorResidual_as_defect {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) (source target : E n) :
    factorResidual H a source target = denominatorHat H a (target - Chat H a source) := by
  rw [map_sub, ← ContinuousLinearMap.mul_apply, denominator_mul_cayley H a hH]
  rfl

theorem denominator_opNorm_le {n : ℕ} (H : Mat n) (a : ℝ) :
    ‖denominatorHat H a‖ ≤ 1 + |a| * ‖operatorOf H‖ := by
  simp only [denominatorHat, cayleyD, skewPart, cscalar, operatorOf, map_add,
    map_one, map_smul]
  calc
    _ ≤ ‖(1 : E n →L[ℂ] E n)‖ + ‖(Complex.I*(a : ℂ)) • operatorOf H‖ := norm_add_le _ _
    _ ≤ 1 + |a| * ‖operatorOf H‖ := by
      simp only [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact add_le_add
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E n)) (le_refl _)

/-- The first two auxiliary states are actual numerical stages. Their zero
residuals leave the final denominator applied to the independently bounded
complete-step defect. No stagewise cancellation is assumed. -/
theorem reduced_stageResidualBudget_bound (h k : ℝ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (v : E 2) :
    stageResidualBudget (2*Real.pi) k (A (Exp006.spatialSymbol h)) B v
      (Chat (A (Exp006.spatialSymbol h)) (k/4) v)
      (Chat B (k/2) (Chat (A (Exp006.spatialSymbol h)) (k/4) v))
      (exactStepHat (A0+B) (k/2) v) ≤
    Real.sqrt (2*Real.pi) * k * (29250*k^2+13*h^2/96) * ‖v‖ := by
  let H := A (Exp006.spatialSymbol h)
  have hH : H.IsHermitian := A_isHermitian _
  have hnorm : ‖operatorOf H‖ ≤ 2 :=
    A_opNorm_le_two _ (spatialSymbol_nonneg h) (spatialSymbol_le_one h (ne_of_gt hh))
  have hd : ‖denominatorHat H (k/4)‖ ≤ 13/12 := by
    have hr := denominator_opNorm_le H (k/4)
    rw [abs_of_nonneg (by positivity : 0 ≤ k/4)] at hr
    nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ k/4 by positivity)]
  have he : ‖exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v‖ ≤
      k*(27000*k^2+h^2/8)*‖v‖ := by
    rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (reduced_local_error h k hh hhsmall hk hksmall)
        (norm_nonneg v))
  change stageResidualBudget (2*Real.pi) k H B v
    (Chat H (k/4) v) (Chat B (k/2) (Chat H (k/4) v))
    (exactStepHat (A0+B) (k/2) v) ≤ _
  simp only [stageResidualBudget, factorResidual_cayley_zero H (k/4) hH,
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add]
  rw [factorResidual_as_defect H (k/4) hH]
  change Real.sqrt (2*Real.pi) * ‖denominatorHat H (k/4)
    (exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v)‖ ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi) * (‖denominatorHat H (k/4)‖ *
        ‖exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2*Real.pi) * ((13/12) * (k*(27000*k^2+h^2/8)*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul hd he (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end NDEAEvolve.Exp007


-- SOURCE lean/FullClosure.lean SHA256 a451d571f0ab42c9d904b6f1a56426272d6e620e57e2f167d648f0f8e67ee2f6

/-! Actual periodic spinor-grid error, with arbitrary numerical initialization. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007
open SpinorGrid

theorem reference_power (v0 : E 2) (k : ℝ) (N : ℕ) :
    (exactStepHat (A0+B) (k/2)^N) v0 = v v0 ((N : ℝ)*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, v_exact_step]
    congr 1
    push_cast
    ring

def gridError (n : ℕ) (h k : ℝ) (N : ℕ) (initial : Vec (Grid n)) (v0 : E 2) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Z X ^ N) initial -
    liftCLM n h (v v0 ((N : ℝ)*k))‖

def initialError (n : ℕ) (h : ℝ) (initial : Vec (Grid n)) (v0 : E 2) : ℝ :=
  Real.sqrt h * ‖initial - liftCLM n h v0‖

/-- The terminal time is Nk≤T. The initial numerical state may contain any
grid modes; its full weighted initial error is retained. -/
theorem concrete_noncommuting_grid_error (n : ℕ) (h k T : ℝ) (N : ℕ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (initial : Vec (Grid n)) (v0 : E 2) :
    gridError n h k N initial v0 ≤ initialError n h initial v0 +
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
  let S := symmetric n h k Z X
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((S^N) initial) ((S^N) (liftCLM n h v0))
    (liftCLM n h (v v0 ((N : ℝ)*k)))
  have hstable : ‖(S^N) initial - (S^N) (liftCLM n h v0)‖ =
      ‖initial - liftCLM n h v0‖ := by
    rw [← map_sub]
    exact symmetric_pow_norm n h k Z X Z_isHermitian X_isHermitian N _
  have hexact : Real.sqrt h * ‖(S^N) (liftCLM n h v0) -
      liftCLM n h (v v0 ((N : ℝ)*k))‖ ≤
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
    rw [symmetric_pow_weighted_error n h k Z X Z_isHermitian X_isHermitian
      hh.le hmesh N v0 (v v0 ((N : ℝ)*k)), ← reference_power]
    have he := reduced_power_error_apply h k T N hh hhsmall hk hksmall horizon v0
    calc
      _ ≤ Real.sqrt (2*Real.pi)*(T*(27000*k^2+h^2/8)*‖v0‖) :=
        mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
      _ = _ := by ring
  change Real.sqrt h * _ ≤ Real.sqrt h * _ + _
  rw [hstable] at htri
  have hb := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg h)
  rw [mul_add] at hb
  exact hb.trans (add_le_add (le_refl _) hexact)

theorem concrete_noncommuting_exact_initial_error (n : ℕ) (h k T : ℝ) (N : ℕ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (v0 : E 2) :
    gridError n h k N (liftCLM n h v0) v0 ≤
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
  simpa [initialError] using concrete_noncommuting_grid_error n h k T N hmesh
    hh hhsmall hk hksmall horizon (liftCLM n h v0) v0

/-- Scalar weighted errors converge even though each mesh has a different
finite-dimensional state space. -/
theorem concrete_noncommuting_mesh_error_tendsto_zero
    (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ) (v0 : E 2)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hmesh : ∀ q, ((n q+1 : ℕ) : ℝ)*h q = 2*Real.pi)
    (hh : ∀ q, 0 < h q) (hhsmall : ∀ q, h q ≤ 1)
    (hk : ∀ q, 0 ≤ k q) (hksmall : ∀ q, k q ≤ 1/6)
    (horizon : ∀ q, (N q : ℝ)*k q ≤ T)
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hinitial : Filter.Tendsto (fun q => initialError (n q) (h q) (initial q) v0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => gridError (n q) (h q) (k q) (N q) (initial q) v0)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => by unfold gridError; positivity)
  · intro q
    exact concrete_noncommuting_grid_error (n q) (h q) (k q) T (N q)
      (hmesh q) (hh q) (hhsmall q) (hk q) (hksmall q) (horizon q) (initial q) v0
  · have hrate := ((hk_limit.pow 2).const_mul 27000).add ((hh_limit.pow 2).div_const 8)
    have hb := hinitial.add ((hrate.const_mul (Real.sqrt (2*Real.pi)*T)).mul_const ‖v0‖)
    simpa using hb

end NDEAEvolve.Exp007


-- SOURCE lean/StageBridge.lean SHA256 7b9c2f68fa999cf08a718a6a11391ba4f6709c235ddb16edc59efe71ab3bd370

/-! The full-grid denominator residual budget equals the existing Exp005
budget on the invariant spinor space, including the physical norm factor. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007
open SpinorGrid

def gridFactorResidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (a : ℝ) (source target : Vec ι) : Vec ι :=
  op (den a H) target - op (num a H) source

def gridStageBudget (n : ℕ) (h k : ℝ)
    (source first second target : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖gridFactorResidual (hamiltonian n h Z) (k/4) source first‖ +
  Real.sqrt h * ‖gridFactorResidual (potential n X) (k/2) first second‖ +
  Real.sqrt h * ‖gridFactorResidual (hamiltonian n h Z) (k/4) second target‖

theorem gridFactorResidual_lift (n : ℕ) (h a : ℝ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (liftCLM n h w) = liftCLM n h (op K w)) (source target : E 2) :
    gridFactorResidual H a (liftCLM n h source) (liftCLM n h target) =
      liftCLM n h (factorResidual K a source target) := by
  rw [gridFactorResidual, den_intertwines (liftCLM n h) H K hJK a target,
    num_intertwines (liftCLM n h) H K hJK a source, ← map_sub]
  rfl

theorem gridFactorResidual_weighted_lift (n : ℕ) (h a : ℝ)
    (hh : 0 ≤ h) (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (liftCLM n h w) = liftCLM n h (op K w)) (source target : E 2) :
    Real.sqrt h * ‖gridFactorResidual H a (liftCLM n h source) (liftCLM n h target)‖ =
      weightedNorm (2*Real.pi) (factorResidual K a source target) := by
  rw [gridFactorResidual_lift n h a H K hJK source target]
  exact lift_weighted_norm n h hh hmesh _

/-- Exact equality with Exp005's actual three-stage residual budget. -/
theorem gridStageBudget_eq_exp005 (n : ℕ) (h k : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi) (source first second target : E 2) :
    gridStageBudget n h k (liftCLM n h source) (liftCLM n h first)
      (liftCLM n h second) (liftCLM n h target) =
    stageResidualBudget (2*Real.pi) k (A (Exp006.spatialSymbol h)) B
      source first second target := by
  unfold gridStageBudget stageResidualBudget
  rw [gridFactorResidual_weighted_lift n h (k/4) hh hmesh _ _
        (hamiltonian_intertwines n h Z hmesh),
      gridFactorResidual_weighted_lift n h (k/2) hh hmesh _ _
        (potential_intertwines n h X),
      gridFactorResidual_weighted_lift n h (k/4) hh hmesh _ _
        (hamiltonian_intertwines n h Z hmesh)]
  rfl

theorem actual_noncommuting_stage_budget (n : ℕ) (h k t : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6) (v0 : E 2) :
    gridStageBudget n h k (liftCLM n h (v v0 t))
      (step (k/4) (hamiltonian n h Z) (liftCLM n h (v v0 t)))
      (step (k/2) (potential n X)
        (step (k/4) (hamiltonian n h Z) (liftCLM n h (v v0 t))))
      (liftCLM n h (v v0 (t+k))) ≤
    Real.sqrt (2*Real.pi)*k*(29250*k^2+13*h^2/96)*‖v0‖ := by
  rw [hamiltonian_step_lift n h (k/4) Z Z_isHermitian hmesh,
    potential_step_lift n h (k/2) X X_isHermitian,
    gridStageBudget_eq_exp005 n h k hh.le hmesh,
    ← v_exact_step v0 t k]
  have hb := reduced_stageResidualBudget_bound h k hh hhsmall hk hksmall (v v0 t)
  rwa [v_norm] at hb

/-- The lifted reference is literally the sampled continuum PDE solution. -/
theorem lift_reference_is_sampled_U (n : ℕ) (h t : ℝ) (v0 : E 2)
    (j : Fin (n+1)) (a : Fin 2) :
    liftCLM n h (v v0 t) (j,a) = U v0 t ((j.val : ℝ)*h) a := rfl

theorem actual_grid_noncommutes (n : ℕ) (h : ℝ) :
    ¬ Commute (hamiltonian n h Z) (potential n X) := by
  apply hamiltonian_noncommutes_potential n h Z X
  simpa [A, B] using A_noncommutes_B 0

end NDEAEvolve.Exp007


-- SOURCE lean/Controls.lean SHA256 32e4f1221d53d0ddd4906cf57c5b57481ddfb67c46fec1b134c9151174ccae8f

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
namespace NDEAEvolve.Exp007.Controls
open SpinorGrid

def initialSpinor : E 2 := WithLp.toLp 2 ![(1 : ℂ), 0]

theorem initialSpinor_norm : ‖initialSpinor‖ = 1 := by
  have hs : ‖initialSpinor‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [initialSpinor, Fin.sum_univ_two]
  nlinarith [norm_nonneg initialSpinor]

theorem admissible_eight_point_grid :
    (0 : ℝ) < Real.pi/4 ∧ Real.pi/4 ≤ 1 ∧
    ((7+1 : ℕ) : ℝ)*(Real.pi/4) = 2*Real.pi ∧
    (0 : ℝ) < 1/12 ∧ (1/12 : ℝ) ≤ 1/6 := by
  refine ⟨by positivity, ?_, ?_, by norm_num, by norm_num⟩
  · linarith [Real.pi_le_four]
  · norm_num <;> ring

theorem coupling_is_active : (operatorOf X initialSpinor) 1 = 1 := by
  norm_num [operatorOf, initialSpinor, X, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem initial_solution_is_spatially_nonconstant :
    U initialSpinor 0 0 ≠ U initialSpinor 0 Real.pi := by
  intro h
  have hc := congrArg (fun w : E 2 => w 0) h
  norm_num [U, v_initial, Exp006.phase, initialSpinor, Complex.exp_pi_mul_I] at hc

theorem omitted_coupling_commutes (lambda : ℝ) : Commute (A lambda) (0 : Mat 2) := by
  exact Commute.zero_right _

theorem zero_mesh_consistency_fails :
    ¬ |Exp006.spatialSymbol 0-1| ≤ (0 : ℝ)^2/8 := by
  norm_num [Exp006.spatialSymbol]

theorem empty_trajectory_retains_initial_error (n : ℕ) (h k : ℝ)
    (initial : Vec (Grid n)) (v0 : E 2) :
    gridError n h k 0 initial v0 = initialError n h initial v0 := by
  simp [gridError, initialError]

end NDEAEvolve.Exp007.Controls


#print axioms NDEAEvolve.Exp007.Z_isHermitian
#print axioms NDEAEvolve.Exp007.X_isHermitian
#print axioms NDEAEvolve.Exp007.A_isHermitian
#print axioms NDEAEvolve.Exp007.B_isHermitian
#print axioms NDEAEvolve.Exp007.A_noncommutes_B
#print axioms NDEAEvolve.Exp007.unitary_opNorm_le_one
#print axioms NDEAEvolve.Exp007.Z_opNorm_le_one
#print axioms NDEAEvolve.Exp007.B_opNorm_le_one
#print axioms NDEAEvolve.Exp007.A_opNorm_le_two
#print axioms NDEAEvolve.Exp007.spatialSymbol_nonneg
#print axioms NDEAEvolve.Exp007.spatialSymbol_le_one
#print axioms NDEAEvolve.Exp007.A_difference_norm_le
#print axioms NDEAEvolve.Exp007.Chat_affine
#print axioms NDEAEvolve.Exp007.resolvent_perturbation_identity
#print axioms NDEAEvolve.Exp007.cayley_perturbation_opNorm_le
#print axioms NDEAEvolve.Exp007.cayley_opNorm_le_one
#print axioms NDEAEvolve.Exp007.symmetric_perturbation_opNorm_le
#print axioms NDEAEvolve.Exp007.reduced_local_error
#print axioms NDEAEvolve.Exp007.SpinorGrid.den_star
#print axioms NDEAEvolve.Exp007.SpinorGrid.den_isUnit
#print axioms NDEAEvolve.Exp007.SpinorGrid.den_mul_resolvent
#print axioms NDEAEvolve.Exp007.SpinorGrid.resolvent_mul_den
#print axioms NDEAEvolve.Exp007.SpinorGrid.den_step
#print axioms NDEAEvolve.Exp007.SpinorGrid.stage_unique
#print axioms NDEAEvolve.Exp007.SpinorGrid.den_intertwines
#print axioms NDEAEvolve.Exp007.SpinorGrid.num_intertwines
#print axioms NDEAEvolve.Exp007.SpinorGrid.step_intertwines
#print axioms NDEAEvolve.Exp007.SpinorGrid.liftCLM_apply
#print axioms NDEAEvolve.Exp007.SpinorGrid.lift_norm_sq
#print axioms NDEAEvolve.Exp007.SpinorGrid.lift_weighted_norm
#print axioms NDEAEvolve.Exp007.SpinorGrid.step_mem_unitary
#print axioms NDEAEvolve.Exp007.SpinorGrid.potential_isHermitian
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_isHermitian
#print axioms NDEAEvolve.Exp007.SpinorGrid.potential_apply
#print axioms NDEAEvolve.Exp007.SpinorGrid.laplacian_apply
#print axioms NDEAEvolve.Exp007.SpinorGrid.potential_intertwines
#print axioms NDEAEvolve.Exp007.SpinorGrid.laplacian_lift
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_intertwines
#print axioms NDEAEvolve.Exp007.SpinorGrid.scalar_add_isHermitian
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_step_lift
#print axioms NDEAEvolve.Exp007.SpinorGrid.potential_step_lift
#print axioms NDEAEvolve.Exp007.SpinorGrid.symmetric_mem_unitary
#print axioms NDEAEvolve.Exp007.SpinorGrid.symmetric_pow_norm
#print axioms NDEAEvolve.Exp007.SpinorGrid.symmetric_lift
#print axioms NDEAEvolve.Exp007.SpinorGrid.symmetric_pow_lift
#print axioms NDEAEvolve.Exp007.SpinorGrid.symmetric_pow_weighted_error
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_apply_stencil
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_mul_potential
#print axioms NDEAEvolve.Exp007.SpinorGrid.potential_mul_hamiltonian
#print axioms NDEAEvolve.Exp007.SpinorGrid.hamiltonian_noncommutes_potential
#print axioms NDEAEvolve.Exp007.continuumPropagator_eq_exactStepHat
#print axioms NDEAEvolve.Exp007.continuumPropagator_add
#print axioms NDEAEvolve.Exp007.continuumEvolution_hasDerivAt
#print axioms NDEAEvolve.Exp007.v_initial
#print axioms NDEAEvolve.Exp007.U_initial
#print axioms NDEAEvolve.Exp007.U_periodic
#print axioms NDEAEvolve.Exp007.v_hasDerivAt
#print axioms NDEAEvolve.Exp007.U_time_hasDerivAt
#print axioms NDEAEvolve.Exp007.U_space_hasDerivAt
#print axioms NDEAEvolve.Exp007.U_second_derivative
#print axioms NDEAEvolve.Exp007.v_norm
#print axioms NDEAEvolve.Exp007.U_norm
#print axioms NDEAEvolve.Exp007.U_schrodinger
#print axioms NDEAEvolve.Exp007.v_exact_step
#print axioms NDEAEvolve.Exp007.reduced_power_error
#print axioms NDEAEvolve.Exp007.reduced_power_error_apply
#print axioms NDEAEvolve.Exp007.denominator_mul_cayley
#print axioms NDEAEvolve.Exp007.factorResidual_cayley_zero
#print axioms NDEAEvolve.Exp007.factorResidual_as_defect
#print axioms NDEAEvolve.Exp007.denominator_opNorm_le
#print axioms NDEAEvolve.Exp007.reduced_stageResidualBudget_bound
#print axioms NDEAEvolve.Exp007.reference_power
#print axioms NDEAEvolve.Exp007.concrete_noncommuting_grid_error
#print axioms NDEAEvolve.Exp007.concrete_noncommuting_exact_initial_error
#print axioms NDEAEvolve.Exp007.concrete_noncommuting_mesh_error_tendsto_zero
#print axioms NDEAEvolve.Exp007.gridFactorResidual_lift
#print axioms NDEAEvolve.Exp007.gridFactorResidual_weighted_lift
#print axioms NDEAEvolve.Exp007.gridStageBudget_eq_exp005
#print axioms NDEAEvolve.Exp007.actual_noncommuting_stage_budget
#print axioms NDEAEvolve.Exp007.lift_reference_is_sampled_U
#print axioms NDEAEvolve.Exp007.actual_grid_noncommutes
#print axioms NDEAEvolve.Exp007.Controls.initialSpinor_norm
#print axioms NDEAEvolve.Exp007.Controls.admissible_eight_point_grid
#print axioms NDEAEvolve.Exp007.Controls.coupling_is_active
#print axioms NDEAEvolve.Exp007.Controls.initial_solution_is_spatially_nonconstant
#print axioms NDEAEvolve.Exp007.Controls.omitted_coupling_commutes
#print axioms NDEAEvolve.Exp007.Controls.zero_mesh_consistency_fails
#print axioms NDEAEvolve.Exp007.Controls.empty_trajectory_retains_initial_error
