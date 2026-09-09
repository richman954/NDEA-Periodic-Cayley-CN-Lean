import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
import Mathlib.Topology.MetricSpace.Pseudo.Basic

-- SOURCE lean/Exp012Foundation.lean SHA256 ff98d87926fe6729202d77119d84e3ff3b3a3664ab607c0069a52db2c9f8547d

-- SOURCE lean/Exp011Foundation.lean SHA256 6e516d1a5cbd1eae23feddcb9b26a29c12a15a6a0d45928c891acd9be453e3e5

-- SOURCE lean/Exp010Foundation.lean SHA256 fb7b27b42d0baaca9ab8b30f9ba80bb0a5b8999986342fe8538e880bb3947ef0

-- SOURCE lean/Exp009Foundation.lean SHA256 8cbf781d91f3cd0cc5f6669586c55a4c4613d6f3e9f322e10fbafff39991e8c8

-- SOURCE lean/Exp008Foundation.lean SHA256 5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0

-- SOURCE lean/Exp007Foundation.lean SHA256 cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c

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




-- SOURCE lean/FrequencyBounds.lean SHA256 97cd20e3dd29cc9b3e663239fb79dd9aa70e721b5e3fed1dd65fa766c2a094c6

/-! Frequency-dependent consistency bounds for finitely supported periodic
spinor data. The cutoff constants remain independent of the grid size. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
open NDEAEvolve.Exp007
namespace NDEAEvolve.Exp008

def modeSymbol (m : ℤ) (h : ℝ) : ℝ := (2-2*Real.cos ((m:ℝ)*h))/h^2
def Ct (M : ℕ) : ℝ := 1000*((M:ℝ)^2+2)^3
def Cs (M : ℕ) : ℝ := (M:ℝ)^4/8

theorem Ct_nonneg (M : ℕ) : 0 ≤ Ct M := by unfold Ct; positivity
theorem Cs_nonneg (M : ℕ) : 0 ≤ Cs M := by unfold Cs; positivity

@[simp] theorem modeSymbol_zero (h : ℝ) : modeSymbol 0 h = 0 := by
  simp [modeSymbol]

theorem modeSymbol_neg (m : ℤ) (h : ℝ) : modeSymbol (-m) h = modeSymbol m h := by
  simp [modeSymbol, neg_mul]

theorem modeSymbol_nonneg (m : ℤ) (h : ℝ) : 0 ≤ modeSymbol m h := by
  unfold modeSymbol
  exact div_nonneg (by linarith [Real.cos_le_one ((m:ℝ)*h)]) (sq_nonneg h)

theorem modeSymbol_le_sq (m : ℤ) (h : ℝ) : modeSymbol m h ≤ (m:ℝ)^2 := by
  by_cases hh : h = 0
  · simp [modeSymbol, hh, sq_nonneg]
  · unfold modeSymbol
    apply (div_le_iff₀ (sq_pos_of_ne_zero hh)).2
    have hc := Real.one_sub_sq_div_two_le_cos (x := (m:ℝ)*h)
    nlinarith

/-- Includes zero and negative frequencies. No division by the frequency is used. -/
theorem modeSymbol_consistency (m : ℤ) (h : ℝ) (hh : 0 < h)
    (hsmall : |(m:ℝ)| * h ≤ 1) :
    |modeSymbol m h-(m:ℝ)^2| ≤ (m:ℝ)^4*h^2/8 := by
  have hx : |(m:ℝ)*h| ≤ 1 := by
    rwa [abs_mul, abs_of_pos hh]
  have hc := Real.cos_bound (x := (m:ℝ)*h) hx
  have hab4 : |(m:ℝ)*h|^4 = (m:ℝ)^4*h^4 := by
    rw [← abs_pow, mul_pow, abs_of_nonneg (by positivity)]
  rw [hab4] at hc
  have he : modeSymbol m h-(m:ℝ)^2 =
      -2*(Real.cos ((m:ℝ)*h)-(1-((m:ℝ)*h)^2/2))/h^2 := by
    unfold modeSymbol
    field_simp
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hh)]
  norm_num
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  nlinarith [show 0 ≤ (m:ℝ)^4*h^4 by positivity]

theorem A_opNorm_le (lambda : ℝ) (hl : 0 ≤ lambda) :
    ‖operatorOf (A lambda)‖ ≤ lambda+1 := by
  have hid : ‖(1 : E 2 →L[ℂ] E 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simp only [A, operatorOf, map_add, map_smul, map_one]
  calc
    _ ≤ ‖(lambda:ℂ) • (1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := norm_add_le _ _
    _ = lambda * ‖(1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    _ ≤ lambda*1+1 := add_le_add
      (mul_le_mul_of_nonneg_left hid hl) Z_opNorm_le_one
    _ = _ := by ring

theorem frequency_sq_le (M : ℕ) (m : ℤ) (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    (m:ℝ)^2 ≤ (M:ℝ)^2 := by
  calc
    _ = |(m:ℝ)|^2 := (sq_abs _).symm
    _ ≤ (M:ℝ)^2 := by gcongr

theorem frequency_fourth_le (M : ℕ) (m : ℤ) (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    (m:ℝ)^4 ≤ (M:ℝ)^4 := by
  have hs := frequency_sq_le M m hm
  nlinarith [sq_nonneg ((M:ℝ)^2-(m:ℝ)^2)]

theorem frequency_generator_norm_le (M : ℕ) (m : ℤ) (h : ℝ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    ‖operatorOf (A (modeSymbol m h))‖ ≤ (M:ℝ)^2+1 := by
  have ha := A_opNorm_le (modeSymbol m h) (modeSymbol_nonneg m h)
  have hs := modeSymbol_le_sq m h
  have hm2 := frequency_sq_le M m hm
  linarith

/-- The time-step hypothesis depends on the fixed spectral cutoff, not mesh norms. -/
theorem frequency_local_error (M : ℕ) (m : ℤ) (h k : ℝ)
    (_hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) :
    ‖symmetricStepHat (A (modeSymbol m h)) B k -
      exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ ≤
      k*(Ct M*k^2+Cs M*h^2) := by
  have hm2 := frequency_sq_le M m hm
  have hm4 := frequency_fourth_le M m hm
  have hsmall : |(m:ℝ)| * h ≤ 1 :=
    (mul_le_mul_of_nonneg_right hm hh.le).trans hMh
  have ha := A_opNorm_le ((m:ℝ)^2) (sq_nonneg _)
  have hb := B_opNorm_le_one
  have hsum : ‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖ ≤ (M:ℝ)^2+2 := by
    linarith
  have hs : 2*|k| * (‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖) ≤ 1 := by
    rw [abs_of_nonneg hk]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hstep
  have ht := symmetric_cayley_exp_local_opNorm_le k (A ((m:ℝ)^2)) B
    (A_isHermitian _) B_isHermitian hs
  have hcube : (‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖)^3 ≤
      ((M:ℝ)^2+2)^3 := by gcongr
  have htemp : ‖symmetricStepHat (A ((m:ℝ)^2)) B k-
      exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ ≤ Ct M*k^3 := by
    rw [abs_of_nonneg hk] at ht
    have hp := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 1000*k^3 by positivity)
    unfold Ct
    nlinarith
  have hspatial : |modeSymbol m h-(m:ℝ)^2| ≤ Cs M*h^2 := by
    have hc := modeSymbol_consistency m h hh hsmall
    have hp := mul_le_mul_of_nonneg_right hm4 (sq_nonneg h)
    unfold Cs
    nlinarith
  have hspace : ‖symmetricStepHat (A (modeSymbol m h)) B k-
      symmetricStepHat (A ((m:ℝ)^2)) B k‖ ≤ k*(Cs M*h^2) := by
    have hp := symmetric_perturbation_opNorm_le (modeSymbol m h) ((m:ℝ)^2) k
    rw [abs_of_nonneg hk] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left hspatial hk)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat (A (modeSymbol m h)) B k)
    (symmetricStepHat (A ((m:ℝ)^2)) B k)
    (exactStepHat (A ((m:ℝ)^2)+B) (k/2))
  nlinarith

theorem frequency_power_error (M : ℕ) (m : ℤ) (h k T : ℝ) (N : ℕ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    ‖symmetricStepHat (A (modeSymbol m h)) B k ^ N-
      exactStepHat (A ((m:ℝ)^2)+B) (k/2) ^ N‖ ≤
      T*(Ct M*k^2+Cs M*h^2) := by
  calc
    _ ≤ (N:ℝ) * ‖symmetricStepHat (A (modeSymbol m h)) B k-
        exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ :=
      unitary_pow_sub_pow_opNorm_le _ _ N
        (symmetricStepHat_mem_unitary k _ _ (A_isHermitian _) B_isHermitian)
        (exactStepHat_mem_unitary (k/2) _ ((A_isHermitian _).add B_isHermitian))
    _ ≤ (N:ℝ) * (k*(Ct M*k^2+Cs M*h^2)) :=
      mul_le_mul_of_nonneg_left
        (frequency_local_error M m h k hM hm hh hMh hk hstep) (Nat.cast_nonneg N)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right horizon
        (add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
          (mul_nonneg (Cs_nonneg M) (sq_nonneg h)))

theorem frequency_denominator_opNorm_le (M : ℕ) (m : ℤ) (h k : ℝ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) :
    ‖denominatorHat (A (modeSymbol m h)) (k/4)‖ ≤ 9/8 := by
  have hd := denominator_opNorm_le (A (modeSymbol m h)) (k/4)
  rw [abs_of_nonneg (by positivity : 0 ≤ k/4)] at hd
  have hn := frequency_generator_norm_le M m h hm
  have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ k/4 by positivity)
  nlinarith

/-- Actual numerical auxiliary stages discharge the measured Exp005 budget. -/
theorem frequency_stageResidualBudget_bound (dx : ℝ) (M : ℕ) (m : ℤ) (h k : ℝ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (v : E 2) :
    stageResidualBudget dx k (A (modeSymbol m h)) B v
      (Chat (A (modeSymbol m h)) (k/4) v)
      (Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) v))
      (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v) ≤
      Real.sqrt dx*(9/8)*k*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
  let H := A (modeSymbol m h)
  have hH : H.IsHermitian := A_isHermitian _
  have hd : ‖denominatorHat H (k/4)‖ ≤ 9/8 :=
    frequency_denominator_opNorm_le M m h k hm hk hstep
  have he : ‖exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v‖ ≤
      k*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
    rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (frequency_local_error M m h k hM hm hh hMh hk hstep) (norm_nonneg v))
  change stageResidualBudget dx k H B v (Chat H (k/4) v)
    (Chat B (k/2) (Chat H (k/4) v)) (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v) ≤ _
  simp only [stageResidualBudget, factorResidual_cayley_zero H (k/4) hH,
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add]
  rw [factorResidual_as_defect H (k/4) hH]
  change Real.sqrt dx*‖denominatorHat H (k/4)
    (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v)‖ ≤ _
  calc
    _ ≤ Real.sqrt dx*(‖denominatorHat H (k/4)‖*
        ‖exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt dx*((9/8)*(k*(Ct M*k^2+Cs M*h^2)*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul hd he (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end NDEAEvolve.Exp008


-- SOURCE lean/ContinuumModes.lean SHA256 9d0f3b6a75aa17a62b023743676f348740ae391fad326aee7fe8d6edf4c65e63

/-! Finite Fourier superpositions of the spinor Schrödinger equation.
Every frequency is an arbitrary signed integer; no separation or non-aliasing
assumption is needed for this continuum construction. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp008

local instance (n : ℕ) : NormedAlgebra ℚ (E n →L[ℂ] E n) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E n →L[ℂ] E n)

def modeGenerator (m : ℤ) : Mat 2 := Exp007.A ((m : ℝ)^2) + Exp007.B

theorem modeGenerator_isHermitian (m : ℤ) : (modeGenerator m).IsHermitian :=
  (Exp007.A_isHermitian _).add Exp007.B_isHermitian

def modeOrbit (m : ℤ) (t : ℝ) (v : E 2) : E 2 :=
  exactStepHat (modeGenerator m) (t / 2) v

theorem modeOrbit_eq_continuum (m : ℤ) (t : ℝ) (v : E 2) :
    modeOrbit m t v = Exp007.continuumPropagator (modeGenerator m) t v := by
  rw [Exp007.continuumPropagator_eq_exactStepHat]
  rfl

@[simp] theorem modeOrbit_initial (m : ℤ) (v : E 2) : modeOrbit m 0 v = v := by
  rw [modeOrbit_eq_continuum]
  have hz : (0 : ℂ) • operatorOf (modeGenerator m) = (0 : E 2 →L[ℂ] E 2) := by
    apply ContinuousLinearMap.ext
    intro w
    change (0 : ℂ) • operatorOf (modeGenerator m) w = 0
    simp
  simp only [Exp007.continuumPropagator, Complex.ofReal_zero, mul_zero]
  rw [hz, NormedSpace.exp_zero]
  rfl

theorem modeOrbit_hasDerivAt (m : ℤ) (v : E 2) (t : ℝ) :
    HasDerivAt (fun s => modeOrbit m s v)
      ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t v)) t := by
  simpa only [modeOrbit_eq_continuum] using
    Exp007.continuumEvolution_hasDerivAt (modeGenerator m) v t

@[simp] theorem modeOrbit_norm (m : ℤ) (t : ℝ) (v : E 2) :
    ‖modeOrbit m t v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (exactStepHat_mem_unitary (t / 2) (modeGenerator m) (modeGenerator_isHermitian m)) v

theorem modeOrbit_exact_step (m : ℤ) (v : E 2) (t k : ℝ) :
    exactStepHat (modeGenerator m) (k / 2) (modeOrbit m t v) =
      modeOrbit m (t + k) v := by
  rw [modeOrbit_eq_continuum, modeOrbit_eq_continuum,
    ← Exp007.continuumPropagator_eq_exactStepHat, add_comm t k,
    Exp007.continuumPropagator_add, ContinuousLinearMap.mul_apply]

def modeSolution (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  Exp006.phase ((m : ℝ) * x) • modeOrbit m t v

theorem phaseMode_periodic (m : ℤ) :
    Function.Periodic (fun x : ℝ => Exp006.phase ((m : ℝ) * x)) (2 * Real.pi) := by
  intro x
  simpa only [mul_add] using (Exp006.phase_periodic.int_mul m) ((m : ℝ) * x)

theorem phaseMode_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Exp006.phase ((m : ℝ) * y))
      (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) x := by
  simpa [Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using!
    (Exp006.phase_hasDerivAt ((m : ℝ) * x)).scomp x
      ((hasDerivAt_id x).const_mul (m : ℝ))

@[simp] theorem modeSolution_initial (m : ℤ) (v : E 2) (x : ℝ) :
    modeSolution m v 0 x = Exp006.phase ((m : ℝ) * x) • v := by
  simp [modeSolution]

theorem modeSolution_periodic (m : ℤ) (v : E 2) (t : ℝ) :
    Function.Periodic (modeSolution m v t) (2 * Real.pi) := by
  intro x
  simp only [modeSolution, phaseMode_periodic m x]

@[simp] theorem modeSolution_norm (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSolution m v t x‖ = ‖v‖ := by
  simp [modeSolution, norm_smul]

theorem modeSolution_time_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (fun s => modeSolution m v s x)
      (Exp006.phase ((m : ℝ) * x) •
        ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t v))) t := by
  exact (modeOrbit_hasDerivAt m v t).const_smul (Exp006.phase ((m : ℝ) * x))

theorem modeSolution_space_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSolution m v t)
      ((Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) • modeOrbit m t v) x :=
  (phaseMode_hasDerivAt m x).smul_const _

theorem modeSolution_second_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (deriv (modeSolution m v t))
      (-((m : ℂ)^2) • modeSolution m v t x) x := by
  have hd : deriv (modeSolution m v t) = fun y =>
      (Exp006.phase ((m : ℝ) * y) * Complex.I * (m : ℂ)) • modeOrbit m t v :=
    funext fun y => (modeSolution_space_hasDerivAt m v t y).deriv
  rw [hd]
  have hc : (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) *
      Complex.I * (m : ℂ) = -((m : ℂ)^2) * Exp006.phase ((m : ℝ) * x) := by
    calc
      _ = (Complex.I * Complex.I) * ((m : ℂ)^2 * Exp006.phase ((m : ℝ) * x)) := by ring
      _ = _ := by simp
  simpa only [modeSolution, smul_smul, hc] using
    (((phaseMode_hasDerivAt m x).mul_const Complex.I).mul_const (m : ℂ)).smul_const
      (modeOrbit m t v)

theorem modeSolution_second_derivative (m : ℤ) (v : E 2) (t x : ℝ) :
    deriv (deriv (modeSolution m v t)) x = -((m : ℂ)^2) • modeSolution m v t x :=
  (modeSolution_second_hasDerivAt m v t x).deriv

theorem modeGenerator_apply (m : ℤ) (w : E 2) :
    operatorOf (modeGenerator m) w =
      (m : ℂ)^2 • w + operatorOf (Exp007.Z + Exp007.X) w := by
  simp [modeGenerator, Exp007.A, Exp007.B, operatorOf, add_assoc]

/-- The PDE uses the actual first real time derivative and second real space derivative. -/
theorem modeSolution_schrodinger (m : ℤ) (v : E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => modeSolution m v s x) t =
      -deriv (deriv (modeSolution m v t)) x +
        operatorOf (Exp007.Z + Exp007.X) (modeSolution m v t x) := by
  rw [(modeSolution_time_hasDerivAt m v t x).deriv, modeSolution_second_derivative]
  have hi : Complex.I * (Exp006.phase ((m : ℝ) * x) * (-Complex.I)) =
      Exp006.phase ((m : ℝ) * x) := by
    calc
      _ = -(Complex.I * Complex.I) * Exp006.phase ((m : ℝ) * x) := by ring
      _ = _ := by simp
  rw [smul_smul, smul_smul, mul_assoc, hi, modeGenerator_apply]
  simp [modeSolution, smul_add, smul_smul, mul_comm]

def finiteSolution (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  ∑ m ∈ S, modeSolution m (a m) t x

@[simp] theorem finiteSolution_initial (S : Finset ℤ) (a : ℤ → E 2) (x : ℝ) :
    finiteSolution S a 0 x = ∑ m ∈ S, Exp006.phase ((m : ℝ) * x) • a m := by
  simp [finiteSolution]

theorem finiteSolution_periodic (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    Function.Periodic (finiteSolution S a t) (2 * Real.pi) := by
  intro x
  exact Finset.sum_congr rfl fun m _ => modeSolution_periodic m (a m) t x

theorem finiteSolution_time_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (fun s => finiteSolution S a s x)
      (∑ m ∈ S, Exp006.phase ((m : ℝ) * x) •
        ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t (a m)))) t :=
  HasDerivAt.fun_sum fun m _ => modeSolution_time_hasDerivAt m (a m) t x

theorem finiteSolution_space_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (finiteSolution S a t)
      (∑ m ∈ S, (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) •
        modeOrbit m t (a m)) x :=
  HasDerivAt.fun_sum fun m _ => modeSolution_space_hasDerivAt m (a m) t x

theorem finiteSolution_derivative_sum (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    deriv (finiteSolution S a t) = fun x => ∑ m ∈ S, deriv (modeSolution m (a m) t) x := by
  funext x
  rw [(finiteSolution_space_hasDerivAt S a t x).deriv]
  exact Finset.sum_congr rfl fun m _ => (modeSolution_space_hasDerivAt m (a m) t x).deriv.symm

theorem finiteSolution_second_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (deriv (finiteSolution S a t))
      (∑ m ∈ S, -((m : ℂ)^2) • modeSolution m (a m) t x) x := by
  rw [finiteSolution_derivative_sum]
  exact HasDerivAt.fun_sum fun m _ => modeSolution_second_hasDerivAt m (a m) t x

theorem finiteSolution_second_derivative (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    deriv (deriv (finiteSolution S a t)) x =
      ∑ m ∈ S, -((m : ℂ)^2) • modeSolution m (a m) t x :=
  (finiteSolution_second_hasDerivAt S a t x).deriv

/-- Every finite signed Fourier superposition solves the same continuum PDE. -/
theorem finiteSolution_schrodinger (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => finiteSolution S a s x) t =
      -deriv (deriv (finiteSolution S a t)) x +
        operatorOf (Exp007.Z + Exp007.X) (finiteSolution S a t x) := by
  rw [(finiteSolution_time_hasDerivAt S a t x).deriv, finiteSolution_second_derivative]
  simp only [finiteSolution, Finset.smul_sum, map_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simpa only [(modeSolution_time_hasDerivAt m (a m) t x).deriv,
    modeSolution_second_derivative] using modeSolution_schrodinger m (a m) t x

end NDEAEvolve.Exp008


-- SOURCE lean/FourierGrid.lean SHA256 c62e4d0498cb5a0af95b3fca52f8407e675c7983c36b1187d7a6c15489a5c5fb

/-! Integer Fourier modes on the actual periodic spinor grid. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp008.FourierGrid

def modeLift (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => phase ((m : ℝ) * ((p.1.val : ℝ) * h)) * v p.2)

def modeLiftLinear (n : ℕ) (h : ℝ) (m : ℤ) : E 2 →ₗ[ℂ] Vec (Grid n) where
  toFun := modeLift n h m
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

def modeLiftCLM (n : ℕ) (h : ℝ) (m : ℤ) : E 2 →L[ℂ] Vec (Grid n) :=
  (modeLiftLinear n h m).toContinuousLinearMap

@[simp] theorem modeLiftCLM_apply (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) : modeLiftCLM n h m v = modeLift n h m v := rfl

theorem modeLift_norm_sq (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) :
    ‖modeLift n h m v‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [modeLift, Fintype.sum_prod_type, norm_mul]
  ring

theorem modeLift_weighted_norm (n : ℕ) (h : ℝ) (m : ℤ) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    Real.sqrt h * ‖modeLift n h m v‖ = Real.sqrt (2 * Real.pi) * ‖v‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), modeLift_norm_sq]
  nlinarith [hmesh]


theorem integer_phase_periodic (m : ℤ) :
    Function.Periodic (fun x : ℝ => phase ((m : ℝ) * x)) (2 * Real.pi) := by
  intro x
  change phase ((m : ℝ) * (x + 2 * Real.pi)) = phase ((m : ℝ) * x)
  rw [mul_add]
  exact (phase_periodic.int_mul m) ((m : ℝ) * x)

theorem mode_centeredStencil (m : ℤ) (h x : ℝ) :
    centeredStencil h (fun x => phase ((m : ℝ) * x)) x =
      (modeSymbol m h : ℂ) * phase ((m : ℝ) * x) := by
  have hadd : phase ((m : ℝ)*(x+h)) = phase ((m : ℝ)*x) * phase ((m : ℝ)*h) := by
    rw [mul_add, phase_add]
  have hsub : phase ((m : ℝ)*(x-h)) = phase ((m : ℝ)*x) * phase (-((m : ℝ)*h)) := by
    rw [mul_sub, sub_eq_add_neg, phase_add]
  have hsum : phase ((m : ℝ)*h) + phase (-((m : ℝ)*h)) =
      (2 * Real.cos ((m : ℝ)*h) : ℝ) := by
    rw [phase_formula, phase_formula]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  unfold centeredStencil modeSymbol
  dsimp only
  rw [hadd, hsub]
  push_cast
  calc
    _ = (2-(phase ((m : ℝ)*h)+phase (-((m : ℝ)*h)))) / (h : ℂ)^2 *
        phase ((m : ℝ)*x) := by ring
    _ = _ := by rw [hsum]; push_cast; ring

theorem potential_modeLift (n : ℕ) (h : ℝ) (m : ℤ) (K : Mat 2) (v : E 2) :
    op (potential n K) (modeLiftCLM n h m v) = modeLiftCLM n h m (operatorOf K v) := by
  ext p
  rcases p with ⟨i,a⟩
  rw [potential_apply]
  change (∑ b : Fin 2, K a b * (phase ((m : ℝ)*((i.val : ℝ)*h)) * v b)) =
    phase ((m : ℝ)*((i.val : ℝ)*h)) * (K.mulVec (WithLp.ofLp v) a)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem laplacian_modeLift (n : ℕ) (h : ℝ) (m : ℤ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) (modeLiftCLM n h m v) =
      (modeSymbol m h : ℂ) • modeLiftCLM n h m v := by
  ext p
  rcases p with ⟨i,a⟩
  rw [laplacian_apply]
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((m : ℝ)*((j.val : ℝ)*h)) * v a) i =
      (modeSymbol m h : ℂ) * (phase ((m : ℝ)*((i.val : ℝ)*h)) * v a)
  have hf : Function.Periodic (fun x => phase ((m : ℝ)*x) * v a) (2*Real.pi) := by
    intro x
    change phase ((m : ℝ)*(x + 2 * Real.pi)) * v a = phase ((m : ℝ)*x) * v a
    exact congrArg (fun z : ℂ => z * v a) (integer_phase_periodic m x)
  have hs := PeriodicGrid.matrix_sample_stencil (n := n) (2*Real.pi) h
    (fun x => phase ((m : ℝ)*x) * v a) hf hmesh i
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((m : ℝ)*((j.val : ℝ)*h)) * v a) i = _ at hs
  rw [hs]
  have hc := mode_centeredStencil m h ((i.val : ℝ)*h)
  unfold centeredStencil at hc
  dsimp only at hc
  calc
    _ = ((2*phase ((m : ℝ)*((i.val : ℝ)*h)) - phase ((m : ℝ)*((i.val : ℝ)*h+h)) -
      phase ((m : ℝ)*((i.val : ℝ)*h-h)))/(h : ℂ)^2) * v a := by ring
    _ = _ := by rw [hc]; ring

theorem hamiltonian_modeLift (n : ℕ) (h : ℝ) (m : ℤ) (K : Mat 2)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (hamiltonian n h K) (modeLiftCLM n h m v) =
      modeLiftCLM n h m (operatorOf ((modeSymbol m h : ℂ) • 1 + K) v) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, laplacian_modeLift n h m hmesh,
    potential_modeLift, operatorOf, map_smul, map_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
theorem hamiltonian_step_modeLift (n : ℕ) (h a : ℝ) (m : ℤ) (K : Mat 2) (hK : K.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    step a (hamiltonian n h K) (modeLiftCLM n h m v) =
      modeLiftCLM n h m (Chat ((modeSymbol m h : ℂ) • 1 + K) a v) := by
  exact step_intertwines (modeLiftCLM n h m) (hamiltonian n h K) _
    (hamiltonian_isHermitian n h K hK) (scalar_add_isHermitian _ K hK)
    (hamiltonian_modeLift n h m K hmesh) a v

theorem potential_step_modeLift (n : ℕ) (h a : ℝ) (m : ℤ) (K : Mat 2) (hK : K.IsHermitian)
    (v : E 2) :
    step a (potential n K) (modeLiftCLM n h m v) = modeLiftCLM n h m (Chat K a v) := by
  exact step_intertwines (modeLiftCLM n h m) (potential n K) K
    (potential_isHermitian n K hK) hK (potential_modeLift n h m K) a v
theorem symmetric_modeLift (n : ℕ) (h k : ℝ) (m : ℤ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    symmetric n h k K Q (modeLiftCLM n h m v) =
      modeLiftCLM n h m (symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k v) := by
  simp only [symmetric, symmetricStepHat, ContinuousLinearMap.mul_apply,
    hamiltonian_step_modeLift n h _ m K hK hmesh, potential_step_modeLift n h _ m Q hQ]

theorem symmetric_pow_modeLift (n : ℕ) (h k : ℝ) (m : ℤ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (v : E 2) :
    (symmetric n h k K Q ^ N) (modeLiftCLM n h m v) =
      modeLiftCLM n h m ((symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k ^ N) v) := by
  induction N generalizing v with
  | zero => simp
  | succ N ih =>
    simp only [pow_succ, ContinuousLinearMap.mul_apply,
      symmetric_modeLift n h k m K Q hK hQ hmesh, ih]


def superpositionLift (n : ℕ) (h : ℝ) (S : Finset ℤ) (a : ℤ → E 2) : Vec (Grid n) :=
  ∑ m ∈ S, modeLiftCLM n h m (a m)

theorem symmetric_pow_superposition (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2) :
    (symmetric n h k K Q ^ N) (superpositionLift n h S a) =
      superpositionLift n h S (fun m =>
        (symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k ^ N) (a m)) := by
  simp only [superpositionLift, map_sum, symmetric_pow_modeLift n h k _ K Q hK hQ hmesh]

end NDEAEvolve.Exp008.FourierGrid


-- SOURCE lean/Orthogonality.lean SHA256 f5840adbd334be3953257dfd33c7b0a4648e3598dd111429db665a2de1687671

/-! Exact discrete Fourier orthogonality and Parseval on an alias-free finite band. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008.FourierGrid

theorem phase_nat_mul (x : ℝ) (j : ℕ) : phase ((j : ℝ) * x) = phase x ^ j := by
  unfold phase
  push_cast
  rw [mul_assoc, Complex.exp_nat_mul]

theorem phase_eq_one_iff (x : ℝ) : phase x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) * (2*Real.pi) := by
  rw [phase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hi := congrArg Complex.im hk
    simpa using hi
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    ring

theorem phase_mesh_eq_one_iff_dvd (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (r : ℤ) :
    phase ((r:ℝ)*h)=1 ↔ ((n+1:ℕ):ℤ) ∣ r := by
  have hh : h ≠ 0 := by intro hh; simp [hh] at hmesh
  rw [phase_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k, ?_⟩
    have hr : (r:ℝ) = ((n+1:ℕ):ℝ)*(k:ℝ) := by
      apply mul_right_cancel₀ hh
      rw [hk, ← hmesh]
      ring
    exact_mod_cast hr
  · rintro ⟨k,rfl⟩
    refine ⟨k, ?_⟩
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [mul_assoc, mul_comm (k:ℝ) h, ← mul_assoc, hmesh]
    ring

theorem phase_sum_zero (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (r : ℤ)
    (hr : ¬ ((n+1:ℕ):ℤ) ∣ r) :
    (∑ j : Fin (n+1), phase ((r:ℝ)*((j.val:ℝ)*h)))=0 := by
  have hne : phase ((r:ℝ)*h) ≠ 1 := by
    simpa [phase_mesh_eq_one_iff_dvd n h hmesh r] using hr
  have hp : phase ((r:ℝ)*h)^(n+1)=1 := by
    rw [← phase_nat_mul]
    have he : ((n+1:ℕ):ℝ)*((r:ℝ)*h)=(r:ℝ)*(2*Real.pi) := by rw [← hmesh]; ring
    rw [he]
    exact (phase_eq_one_iff _).mpr ⟨r,rfl⟩
  calc
    _ = ∑ j : Fin (n+1), phase ((r:ℝ)*h)^j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← phase_nat_mul]
      congr 1
      ring
    _ = 0 := by rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne, hp]; simp

theorem band_difference_not_dvd (M n : ℕ) (m l : ℤ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) (hl : |(l:ℝ)| ≤ (M:ℝ))
    (hband : 2*M < n+1) (hne : m ≠ l) : ¬ ((n+1:ℕ):ℤ) ∣ l-m := by
  rintro ⟨k,hk⟩
  have hM : (2:ℝ)*M < (n+1:ℕ) := by exact_mod_cast hband
  have hd : (0:ℝ)<(n+1:ℕ) := by positivity
  have hkr : (l:ℝ)-(m:ℝ)=((n+1:ℕ):ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hsub : |(l:ℝ)-(m:ℝ)| ≤ 2*(M:ℝ) := (abs_sub _ _).trans (by linarith)
  have habsk : |(k:ℝ)| < 1 := by
    rw [hkr, abs_mul, abs_of_pos hd] at hsub
    nlinarith
  have hkb : -1 < k ∧ k < 1 := by exact_mod_cast (abs_lt.mp habsk)
  have hk0 : k=0 := by omega
  simp [hk0] at hk
  omega

theorem phase_conj (x : ℝ) : starRingEnd ℂ (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem mode_product (m l : ℤ) (x : ℝ) (u v : ℂ) :
    (phase ((l:ℝ)*x)*v)*starRingEnd ℂ (phase ((m:ℝ)*x)*u) =
      phase (((l-m:ℤ):ℝ)*x)*(v*starRingEnd ℂ u) := by
  rw [map_mul]
  calc
    _ = (phase ((l:ℝ)*x)*starRingEnd ℂ (phase ((m:ℝ)*x)))*
        (v*starRingEnd ℂ u) := by ring
    _ = _ := by
      rw [phase_conj, ← phase_add]
      congr 2
      push_cast
      ring

theorem modeLift_inner_eq_zero (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (m l : ℤ)
    (hne : ¬ ((n+1:ℕ):ℤ) ∣ l-m) (u v : E 2) :
    inner ℂ (modeLiftCLM n h m u) (modeLiftCLM n h l v) = 0 := by
  change (∑ p : Grid n, (phase ((l:ℝ)*((p.1.val:ℝ)*h))*v p.2)*
    starRingEnd ℂ (phase ((m:ℝ)*((p.1.val:ℝ)*h))*u p.2))=0
  rw [Fintype.sum_prod_type]
  simp only [mode_product]
  have he : (∑ i : Fin (n+1), ∑ b : Fin 2,
      phase (((l-m:ℤ):ℝ)*((i.val:ℝ)*h))*(v b*starRingEnd ℂ (u b))) =
      (∑ i : Fin (n+1), phase (((l-m:ℤ):ℝ)*((i.val:ℝ)*h)))*
        (∑ b : Fin 2, v b*starRingEnd ℂ (u b)) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [he, phase_sum_zero n h hmesh (l-m) hne, zero_mul]

def AliasFree (n : ℕ) (S : Finset ℤ) : Prop :=
  ∀ m ∈ S, ∀ l ∈ S, m ≠ l → ¬ ((n+1:ℕ):ℤ) ∣ l-m

theorem aliasFree_of_band (M n : ℕ) (S : Finset ℤ)
    (hband : 2*M < n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ)) : AliasFree n S := by
  intro m hm l hl hne
  exact band_difference_not_dvd M n m l (hS m hm) (hS l hl) hband hne

theorem superposition_norm_sq (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hS : AliasFree n S) (a : ℤ → E 2) :
    ‖superpositionLift n h S a‖^2 = ((n+1:ℕ):ℝ) * ∑ m ∈ S, ‖a m‖^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [superpositionLift]
  | @insert m S hm ih =>
    have hsub : AliasFree n S := by
      intro l hl r hr hne
      exact hS l (Finset.mem_insert_of_mem hl) r (Finset.mem_insert_of_mem hr) hne
    have horth : inner ℂ (modeLiftCLM n h m (a m)) (superpositionLift n h S a) = 0 := by
      unfold superpositionLift
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro l hl
      exact modeLift_inner_eq_zero n h hmesh m l
        (hS m (Finset.mem_insert_self _ _) l (Finset.mem_insert_of_mem hl)
          (by intro he; exact hm (he.symm ▸ hl))) (a m) (a l)
    have hins : superpositionLift n h (insert m S) a =
        modeLiftCLM n h m (a m)+superpositionLift n h S a := by
      simp [superpositionLift, hm]
    have hpy : ‖modeLiftCLM n h m (a m)+superpositionLift n h S a‖^2 =
        ‖modeLiftCLM n h m (a m)‖^2+‖superpositionLift n h S a‖^2 := by
      simpa only [← pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [hins, hpy,
      modeLiftCLM_apply, modeLift_norm_sq, ih hsub, Finset.sum_insert hm]
    ring

theorem superposition_weighted_norm (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hS : AliasFree n S) (a : ℤ → E 2) :
    Real.sqrt h * ‖superpositionLift n h S a‖ =
      Real.sqrt (2*Real.pi) * Real.sqrt (∑ m ∈ S, ‖a m‖^2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),
    Real.sq_sqrt (Finset.sum_nonneg (fun m _ => sq_nonneg ‖a m‖)),
    superposition_norm_sq n h hmesh S hS a]
  rw [← mul_assoc, mul_comm h, hmesh]

theorem band_superposition_weighted_norm (M n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hband : 2*M < n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ)) (a : ℤ → E 2) :
    Real.sqrt h * ‖superpositionLift n h S a‖ =
      Real.sqrt (2*Real.pi) * Real.sqrt (∑ m ∈ S, ‖a m‖^2) :=
  superposition_weighted_norm n h hh hmesh S (aliasFree_of_band M n S hband hS) a

end NDEAEvolve.Exp008.FourierGrid


-- SOURCE lean/SuperpositionClosure.lean SHA256 a793d4731fa9c01aea6dca1ae4993a73750c426a2168920da1920f2eb130d377

/-! Full-grid error for a fixed finite Fourier spectrum. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008
open FourierGrid

def coefficientNorm (S : Finset ℤ) (a : ℤ → E 2) : ℝ :=
  Real.sqrt (∑ m ∈ S, ‖a m‖^2)

theorem coefficientNorm_nonneg (S : Finset ℤ) (a : ℤ → E 2) :
    0 ≤ coefficientNorm S a := Real.sqrt_nonneg _

theorem coefficientNorm_bound (S : Finset ℤ) (a b : ℤ → E 2) (c : ℝ)
    (hc : 0 ≤ c) (hb : ∀ m ∈ S, ‖b m‖ ≤ c*‖a m‖) :
    coefficientNorm S b ≤ c*coefficientNorm S a := by
  have ha : 0 ≤ ∑ m ∈ S, ‖a m‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ m ∈ S, ‖b m‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (coefficientNorm_nonneg S b)
    (mul_nonneg hc (coefficientNorm_nonneg S a))).mp
  unfold coefficientNorm
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb0]
  calc
    _ ≤ ∑ m ∈ S, (c*‖a m‖)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (norm_nonneg _) (hb m hm) 2
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

@[simp] theorem coefficientNorm_orbit (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    coefficientNorm S (fun m => modeOrbit m t (a m)) = coefficientNorm S a := by
  simp [coefficientNorm]

theorem modeOrbit_power (m : ℤ) (v : E 2) (k : ℝ) (N : ℕ) :
    (exactStepHat (modeGenerator m) (k/2)^N) v = modeOrbit m ((N:ℝ)*k) v := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, modeOrbit_exact_step]
    congr 1
    push_cast
    ring

theorem superpositionLift_sub (n : ℕ) (h : ℝ) (S : Finset ℤ) (a b : ℤ → E 2) :
    superpositionLift n h S a - superpositionLift n h S b =
      superpositionLift n h S (fun m => a m-b m) := by
  simp only [superpositionLift, map_sub, Finset.sum_sub_distrib]

theorem superposition_is_sampled_solution (n : ℕ) (h : ℝ) (S : Finset ℤ)
    (a : ℤ → E 2) (t : ℝ) (p : Grid n) :
    superpositionLift n h S (fun m => modeOrbit m t (a m)) p =
      finiteSolution S a t ((p.1.val:ℝ)*h) p.2 := by
  simp [superpositionLift, modeLiftCLM, modeLiftLinear, modeLift,
    finiteSolution, modeSolution, mul_assoc]

theorem frequency_power_error_apply (M : ℕ) (m : ℤ) (h k T : ℝ) (N : ℕ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) (v : E 2) :
    ‖(symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) v-
      modeOrbit m ((N:ℝ)*k) v‖ ≤ T*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
  rw [← modeOrbit_power m v k N]
  change ‖(symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) v-
    (exactStepHat (Exp007.A ((m:ℝ)^2)+Exp007.B) (k/2)^N) v‖ ≤ _
  rw [← ContinuousLinearMap.sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (frequency_power_error M m h k T N hM hm hh hMh hk hstep horizon) (norm_nonneg v))

def finiteGridError (n : ℕ) (h k : ℝ) (N : ℕ) (S : Finset ℤ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial-
    superpositionLift n h S (fun m => modeOrbit m ((N:ℝ)*k) (a m))‖

def finiteInitialError (n : ℕ) (h : ℝ) (S : Finset ℤ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial-superpositionLift n h S a‖

theorem finite_superposition_exact_initial_error (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hM : 1 ≤ M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    finiteGridError n h k N S a (superpositionLift n h S a) ≤
      Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let b := fun m => (symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) (a m)-
    modeOrbit m ((N:ℝ)*k) (a m)
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  have hc : 0 ≤ T*(Ct M*k^2+Cs M*h^2) :=
    mul_nonneg hT (add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
      (mul_nonneg (Cs_nonneg M) (sq_nonneg h)))
  have hb : coefficientNorm S b ≤ T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a :=
    coefficientNorm_bound S a b _ hc fun m hm =>
      frequency_power_error_apply M m h k T N hM (hS m hm) hh hMh hk hstep horizon (a m)
  unfold finiteGridError
  rw [symmetric_pow_superposition n h k Exp007.Z Exp007.X
    Exp007.Z_isHermitian Exp007.X_isHermitian hmesh N S a, superpositionLift_sub]
  change Real.sqrt h*‖superpositionLift n h S b‖ ≤ _
  rw [band_superposition_weighted_norm M n h hh.le hmesh S hband hS b]
  change Real.sqrt (2*Real.pi)*coefficientNorm S b ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The numerical initial state may contain any grid frequencies; retain its entire error. -/
theorem finite_superposition_grid_error (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2) (initial : Vec (Grid n))
    (hM : 1 ≤ M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    finiteGridError n h k N S a initial ≤ finiteInitialError n h S a initial+
      Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let G := symmetric n h k Exp007.Z Exp007.X
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((G^N) initial) ((G^N) (superpositionLift n h S a))
    (superpositionLift n h S (fun m => modeOrbit m ((N:ℝ)*k) (a m)))
  have hs : ‖(G^N) initial-(G^N) (superpositionLift n h S a)‖ =
      ‖initial-superpositionLift n h S a‖ := by
    rw [← map_sub]
    exact symmetric_pow_norm n h k Exp007.Z Exp007.X
      Exp007.Z_isHermitian Exp007.X_isHermitian N _
  rw [hs] at htri
  have ht := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg h)
  rw [mul_add] at ht
  exact ht.trans (add_le_add (le_refl _) (finite_superposition_exact_initial_error
    M n h k T N S a hM hband hS hmesh hh hMh hk hstep horizon))

/-- The cutoff and spectrum stay fixed while grid dimensions may vary. -/
theorem finite_superposition_mesh_error_tendsto_zero
    (M : ℕ) (S : Finset ℤ) (a : ℤ → E 2) (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hM : 1 ≤ M) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hband : ∀ q, 2*M<n q+1)
    (hmesh : ∀ q, ((n q+1:ℕ):ℝ)*h q=2*Real.pi)
    (hh : ∀ q, 0<h q) (hMh : ∀ q, (M:ℝ)*h q≤1)
    (hk : ∀ q, 0≤k q) (hstep : ∀ q, 2*k q*((M:ℝ)^2+2)≤1)
    (horizon : ∀ q, (N q:ℝ)*k q≤T)
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hi_limit : Filter.Tendsto (fun q => finiteInitialError (n q) (h q) S a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => finiteGridError (n q) (h q) (k q) (N q) S a (initial q))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => by unfold finiteGridError; positivity)
  · intro q
    exact finite_superposition_grid_error M (n q) (h q) (k q) T (N q) S a (initial q)
      hM (hband q) hS (hmesh q) (hh q) (hMh q) (hk q) (hstep q) (horizon q)
  · have hr := ((hk_limit.pow 2).const_mul (Ct M)).add ((hh_limit.pow 2).const_mul (Cs M))
    have hb := hi_limit.add ((hr.const_mul (Real.sqrt (2*Real.pi)*T)).mul_const (coefficientNorm S a))
    simpa using hb

end NDEAEvolve.Exp008


-- SOURCE lean/StageBridge.lean SHA256 85f75baadcbe2c1500463cb82d35b1bede8e8e7c0ea24f0628bf4dcff38cd4c6

/-! The actual full-grid implicit-factor residuals decompose by frequency.
Parseval aggregates the final residual in coefficient ℓ²; the first two
auxiliary states are the actual numerical stages and have zero residual. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
open NDEAEvolve.Exp007 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008
open FourierGrid

theorem gridFactorResidual_modeLift (n : ℕ) (h alpha : ℝ) (m : ℤ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op K w))
    (source target : E 2) :
    gridFactorResidual H alpha (modeLiftCLM n h m source) (modeLiftCLM n h m target) =
      modeLiftCLM n h m (factorResidual K alpha source target) := by
  rw [gridFactorResidual, den_intertwines (modeLiftCLM n h m) H K hJK alpha target,
    num_intertwines (modeLiftCLM n h m) H K hJK alpha source, ← map_sub]
  rfl

/-- Exact linear decomposition of the measured denominator residual. -/
theorem gridFactorResidual_superposition (n : ℕ) (h alpha : ℝ) (S : Finset ℤ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : ℤ → Mat 2)
    (hJK : ∀ m ∈ S, ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op (K m) w))
    (source target : ℤ → E 2) :
    gridFactorResidual H alpha (superpositionLift n h S source) (superpositionLift n h S target) =
      superpositionLift n h S (fun m => factorResidual (K m) alpha (source m) (target m)) := by
  unfold gridFactorResidual superpositionLift
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact gridFactorResidual_modeLift n h alpha m H (K m) (hJK m hm) (source m) (target m)

theorem gridFactorResidual_superposition_weighted_norm (M n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (H : Matrix (Grid n) (Grid n) ℂ) (K : ℤ → Mat 2)
    (source target : ℤ → E 2) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hband : 2*M<n+1)
    (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hJK : ∀ m ∈ S, ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op (K m) w)) :
    Real.sqrt h * ‖gridFactorResidual H alpha
      (superpositionLift n h S source) (superpositionLift n h S target)‖ =
      Real.sqrt (2*Real.pi) * coefficientNorm S
        (fun m => factorResidual (K m) alpha (source m) (target m)) := by
  rw [gridFactorResidual_superposition n h alpha S H K hJK source target]
  exact band_superposition_weighted_norm M n h hh hmesh S hband hS _

theorem hamiltonian_step_superposition (n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    step alpha (hamiltonian n h Z) (superpositionLift n h S a) =
      superpositionLift n h S (fun m => Chat (A (modeSymbol m h)) alpha (a m)) := by
  simp only [A, superpositionLift, map_sum,
    hamiltonian_step_modeLift n h alpha _ Z Z_isHermitian hmesh]

theorem potential_step_superposition (n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2) :
    step alpha (potential n X) (superpositionLift n h S a) =
      superpositionLift n h S (fun m => Chat B alpha (a m)) := by
  simp only [B, superpositionLift, map_sum,
    potential_step_modeLift n h alpha _ X X_isHermitian]

@[simp] theorem gridFactorResidual_step_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (alpha : ℝ) (hH : H.IsHermitian) (v : Vec ι) :
    gridFactorResidual H alpha v (step alpha H v) = 0 := by
  unfold gridFactorResidual
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, den_step alpha H hH, sub_self]

theorem frequency_final_stage_residual_bound (M : ℕ) (m : ℤ) (h k t : ℝ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0<h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0≤k) (hstep : 2*k*((M:ℝ)^2+2)≤1)
    (a : E 2) :
    ‖factorResidual (A (modeSymbol m h)) (k/4)
      (Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) (modeOrbit m t a)))
      (modeOrbit m (t+k) a)‖ ≤ (9/8)*k*(Ct M*k^2+Cs M*h^2)*‖a‖ := by
  have hb := frequency_stageResidualBudget_bound 1 M m h k
    hM hm hh hMh hk hstep (modeOrbit m t a)
  simp only [stageResidualBudget,
    factorResidual_cayley_zero (A (modeSymbol m h)) (k/4) (A_isHermitian _),
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add,
    weightedNorm, Real.sqrt_one, one_mul, norm_zero, modeOrbit_norm] at hb
  rw [← modeOrbit_exact_step m a t k]
  simpa only [modeGenerator] using hb

/-- A derived bound on Exp007's actual full-grid three-stage residual budget.
No triangle sum over Fourier coefficients replaces the coefficient ℓ² norm. -/
theorem actual_superposition_stage_budget (M n : ℕ) (h k t : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hM : 1≤M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)|≤(M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k) (hstep : 2*k*((M:ℝ)^2+2)≤1) :
    gridStageBudget n h k
      (superpositionLift n h S (fun m => modeOrbit m t (a m)))
      (step (k/4) (hamiltonian n h Z)
        (superpositionLift n h S (fun m => modeOrbit m t (a m))))
      (step (k/2) (potential n X) (step (k/4) (hamiltonian n h Z)
        (superpositionLift n h S (fun m => modeOrbit m t (a m)))))
      (superpositionLift n h S (fun m => modeOrbit m (t+k) (a m))) ≤
      Real.sqrt (2*Real.pi)*(9/8)*k*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let b := fun m => modeOrbit m t (a m)
  let q := fun m => Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) (b m))
  let target := fun m => modeOrbit m (t+k) (a m)
  let r := fun m => factorResidual (A (modeSymbol m h)) (k/4) (q m) (target m)
  have hct := Ct_nonneg M
  have hcs := Cs_nonneg M
  have hc : coefficientNorm S r ≤
      ((9/8)*k*(Ct M*k^2+Cs M*h^2))*coefficientNorm S a := by
    apply coefficientNorm_bound S a r _ (by positivity)
    intro m hm
    exact frequency_final_stage_residual_bound M m h k t hM (hS m hm) hh hMh hk hstep (a m)
  have hH := hamiltonian_isHermitian n h Z Z_isHermitian
  have hP := potential_isHermitian n X X_isHermitian
  change gridStageBudget n h k (superpositionLift n h S b)
    (step (k/4) (hamiltonian n h Z) (superpositionLift n h S b))
    (step (k/2) (potential n X) (step (k/4) (hamiltonian n h Z)
      (superpositionLift n h S b))) (superpositionLift n h S target) ≤ _
  simp only [gridStageBudget,
    gridFactorResidual_step_zero (hamiltonian n h Z) (k/4) hH,
    gridFactorResidual_step_zero (potential n X) (k/2) hP,
    norm_zero, mul_zero, zero_add]
  rw [hamiltonian_step_superposition n h (k/4) S b hmesh,
    potential_step_superposition n h (k/2) S]
  change Real.sqrt h*‖gridFactorResidual (hamiltonian n h Z) (k/4)
    (superpositionLift n h S q) (superpositionLift n h S target)‖ ≤ _
  rw [gridFactorResidual_superposition_weighted_norm M n h (k/4) S
    (hamiltonian n h Z) (fun m => A (modeSymbol m h)) q target hh.le hmesh hband hS
    (fun m _ w => hamiltonian_modeLift n h m Z hmesh w)]
  change Real.sqrt (2*Real.pi)*coefficientNorm S r ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi)*(((9/8)*k*(Ct M*k^2+Cs M*h^2))*coefficientNorm S a) :=
      mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
    _ = _ := by ring

end NDEAEvolve.Exp008


-- SOURCE lean/Controls.lean SHA256 51732dae30719c18d67cae31a958aa3544b80199578cb390d79563c72a1f57a5

/-! Concrete controls for signed superpositions, aliasing, initial error,
and frequency-dependent constants. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008.Controls
open FourierGrid

def activeSpectrum : Finset ℤ := {-1, 0, 1}

def activeCoefficients (m : ℤ) : E 2 :=
  (if m = -1 then (1 : ℂ) else if m = 0 then 2 else if m = 1 then 3 else 0) •
    Exp007.Controls.initialSpinor

private theorem active_coefficient_norms :
    ‖activeCoefficients (-1)‖ = 1 ∧ ‖activeCoefficients 0‖ = 2 ∧
      ‖activeCoefficients 1‖ = 3 := by
  norm_num [activeCoefficients, norm_smul, Exp007.Controls.initialSpinor_norm]

/-- All three signed modes are active, and the physical initial data is nonzero. -/
theorem active_signed_superposition :
    (∀ m ∈ activeSpectrum, |(m : ℝ)| ≤ 1 ∧ activeCoefficients m ≠ 0) ∧
    coefficientNorm activeSpectrum activeCoefficients = Real.sqrt 14 ∧
    finiteSolution activeSpectrum activeCoefficients 0 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    have hm' : m = -1 ∨ m = 0 ∨ m = 1 := by simpa [activeSpectrum] using hm
    rcases hm' with rfl | rfl | rfl
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.1]; norm_num)
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.2.1]; norm_num)
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.2.2]; norm_num)
  · norm_num [coefficientNorm, activeSpectrum, active_coefficient_norms.1,
      active_coefficient_norms.2.1, active_coefficient_norms.2.2]
  · intro hz
    have hc := congrArg (fun w : E 2 => w 0) hz
    norm_num [finiteSolution, activeSpectrum, modeSolution_initial,
      activeCoefficients, Exp007.Controls.initialSpinor] at hc

/-- A concrete admissible cutoff-one, eight-point grid with positive timestep. -/
theorem admissible_multimode_grid :
    2 * (1 : ℕ) < 7 + 1 ∧
    (0 : ℝ) < Real.pi / 4 ∧ Real.pi / 4 ≤ 1 ∧
    ((7 + 1 : ℕ) : ℝ) * (Real.pi / 4) = 2 * Real.pi ∧
    (0 : ℝ) < 1 / 12 ∧ 2 * (1 / 12 : ℝ) * ((1 : ℝ)^2 + 2) ≤ 1 := by
  refine ⟨by norm_num, by positivity, ?_, ?_, by norm_num, by norm_num⟩
  · linarith [Real.pi_le_four]
  · norm_num <;> ring

/-- Frequencies separated by the grid size produce the same sampled mode. -/
theorem grid_size_alias (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    modeLift n h 0 v = modeLift n h ((n + 1 : ℕ) : ℤ) v := by
  ext p
  simp only [modeLift, WithLp.ofLp_toLp, Int.cast_zero, Int.cast_natCast]
  have hp : Exp006.phase (((n + 1 : ℕ) : ℝ) * ((p.1.val : ℝ) * h)) = 1 := by
    rw [show ((n + 1 : ℕ) : ℝ) * ((p.1.val : ℝ) * h) =
      (p.1.val : ℝ) * (((n + 1 : ℕ) : ℝ) * h) by ring, hmesh]
    simpa using Exp006.phase_periodic.nat_mul_eq p.1.val
  simp only [Nat.cast_add, Nat.cast_one] at hp
  simp [hp]

/-- Opposite coefficients cancel on aliased modes, invalidating unrestricted Parseval. -/
theorem aliasing_breaks_naive_parseval (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) :
    ‖modeLift n h 0 Exp007.Controls.initialSpinor -
      modeLift n h ((n + 1 : ℕ) : ℤ) Exp007.Controls.initialSpinor‖^2 ≠
      ((n + 1 : ℕ) : ℝ) * (‖Exp007.Controls.initialSpinor‖^2 +
        ‖-Exp007.Controls.initialSpinor‖^2) := by
  rw [grid_size_alias n h hmesh]
  simp [Exp007.Controls.initialSpinor_norm] <;> positivity

/-- No time steps means the entire supplied initial grid error remains. -/
theorem empty_trajectory_retains_initial_error (n : ℕ) (h k : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2) (initial : Vec (Grid n)) :
    finiteGridError n h k 0 S a initial = finiteInitialError n h S a initial := by
  simp [finiteGridError, finiteInitialError]

/-- Superposition does not remove the actual noncommuting full-grid split. -/
theorem full_grid_split_is_noncommuting (n : ℕ) (h : ℝ) :
    ¬ Commute (hamiltonian n h Exp007.Z) (potential n Exp007.X) := by
  apply hamiltonian_noncommutes_potential
  simpa [Exp007.A, Exp007.B] using Exp007.A_noncommutes_B 0

/-- The constants are uniform in the mesh, but grow with the fixed frequency cutoff. -/
theorem frequency_constants_increase : Ct 1 < Ct 2 ∧ Cs 1 < Cs 2 := by
  norm_num [Ct, Cs]

end NDEAEvolve.Exp008.Controls




-- SOURCE lean/InfiniteReference.lean SHA256 ef31378a27fb871f22d662303a86cc8c90c1cc2ea18bb959b770d5cef71a38e1

/-! Infinite absolutely summable Fourier references and an alias-safe sampled tail.
No discrete Parseval identity is asserted for the infinite spectrum. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009

def band (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
def mass (a : ℤ → E 2) : ℝ := ∑' m, ‖a m‖
def tail (M : ℕ) (a : ℤ → E 2) : ℝ :=
  mass a - ∑ m ∈ band M, ‖a m‖
def infiniteSolution (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  ∑' m, modeSolution m (a m) t x
def infiniteGrid (n : ℕ) (h : ℝ) (a : ℤ → E 2) (t : ℝ) : Vec (Grid n) :=
  ∑' m, modeLiftCLM n h m (modeOrbit m t (a m))

theorem band_frequency_bound (M : ℕ) (m : ℤ) (hm : m ∈ band M) :
    |(m : ℝ)| ≤ (M : ℝ) := by
  have h := Finset.mem_Icc.mp hm
  apply abs_le.mpr
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem band_tendsto_atTop :
    Filter.Tendsto band Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro s
  filter_upwards [Filter.eventually_ge_atTop (s.sup Int.natAbs)] with M hM
  intro m hm
  have hn : m.natAbs ≤ M := (Finset.le_sup (f := Int.natAbs) hm).trans hM
  have hab : |m| ≤ (M : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hn
  exact Finset.mem_Icc.mpr (abs_le.mp hab)

theorem mass_nonneg (a : ℤ → E 2) : 0 ≤ mass a :=
  tsum_nonneg fun _ => norm_nonneg _

theorem band_mass_le (M : ℕ) (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    (∑ m ∈ band M, ‖a m‖) ≤ mass a :=
  ha.sum_le_tsum _ (fun _ _ => norm_nonneg _)

theorem tail_nonneg (M : ℕ) (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    0 ≤ tail M a := sub_nonneg.mpr (band_mass_le M a ha)

theorem tail_eq_tsum_compl (M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    tail M a = ∑' m : {m : ℤ // m ∉ band M}, ‖a m‖ := by
  have he := ha.sum_add_tsum_subtype_compl (band M)
  unfold tail mass
  linarith

theorem tail_tendsto_zero (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    Filter.Tendsto (fun M : ℕ => tail M a) Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto (fun M : ℕ => ∑ m ∈ band M, ‖a m‖)
      Filter.atTop (nhds (mass a)) :=
    ha.hasSum.comp band_tendsto_atTop
  simpa [tail] using (tendsto_const_nhds (x := mass a)).sub hs

theorem coefficientNorm_band_le_mass (M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) : coefficientNorm (band M) a ≤ mass a := by
  have hp : coefficientNorm (band M) a ≤ ∑ m ∈ band M, ‖a m‖ := by
    unfold coefficientNorm
    apply (Real.sqrt_le_iff).mpr
    exact ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)⟩
  exact hp.trans (band_mass_le M a ha)

theorem modeSolution_summable_norm (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t x : ℝ) :
    Summable fun m => ‖modeSolution m (a m) t x‖ := by simpa using ha

theorem modeSolution_summable (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t x : ℝ) :
    Summable fun m => modeSolution m (a m) t x :=
  (modeSolution_summable_norm a ha t x).of_norm

theorem infiniteSolution_periodic (a : ℤ → E 2) (t : ℝ) :
    Function.Periodic (infiniteSolution a t) (2 * Real.pi) := by
  intro x
  unfold infiniteSolution
  apply tsum_congr
  intro m
  exact modeSolution_periodic m (a m) t x

theorem infiniteSolution_initial (a : ℤ → E 2) (x : ℝ) :
    infiniteSolution a 0 x = ∑' m : ℤ, Exp006.phase ((m : ℝ) * x) • a m := by
  simp [infiniteSolution]

theorem modeLift_norm (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) :
    ‖modeLiftCLM n h m v‖ = Real.sqrt ((n+1 : ℕ) : ℝ) * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact modeLift_norm_sq n h m v

theorem infiniteGrid_summable_norm (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) :
    Summable fun m => ‖modeLiftCLM n h m (modeOrbit m t (a m))‖ := by
  simp only [modeLift_norm, modeOrbit_norm]
  exact ha.mul_left _

theorem infiniteGrid_summable (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) :
    Summable fun m => modeLiftCLM n h m (modeOrbit m t (a m)) :=
  (infiniteGrid_summable_norm n h a ha t).of_norm

theorem infiniteGrid_initial (n : ℕ) (h : ℝ) (a : ℤ → E 2) :
    infiniteGrid n h a 0 = ∑' m, modeLiftCLM n h m (a m) := by
  simp [infiniteGrid]

theorem infiniteGrid_is_sampled_solution (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) (p : Grid n) :
    infiniteGrid n h a t p = infiniteSolution a t ((p.1.val : ℝ) * h) p.2 := by
  have hg := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Grid n => ℂ) p).map_tsum
    (infiniteGrid_summable n h a ha t)
  have hs := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) p.2).map_tsum
    (modeSolution_summable a ha t ((p.1.val : ℝ) * h))
  change infiniteGrid n h a t p =
    ∑' m, (modeLiftCLM n h m (modeOrbit m t (a m))) p at hg
  change infiniteSolution a t ((p.1.val : ℝ)*h) p.2 =
    ∑' m, modeSolution m (a m) t ((p.1.val : ℝ)*h) p.2 at hs
  exact hg.trans ((tsum_congr fun _ => rfl).trans hs.symm)

theorem infiniteGrid_tail_bound (M n : ℕ) (h : ℝ) (a : ℤ → E 2) (t : ℝ)
    (ha : Summable fun m => ‖a m‖) (hh : 0 < h)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi) :
    Real.sqrt h * ‖infiniteGrid n h a t -
      superpositionLift n h (band M) (fun m => modeOrbit m t (a m))‖ ≤
      Real.sqrt (2*Real.pi)*tail M a := by
  have hs := infiniteGrid_summable n h a ha t
  have hn := infiniteGrid_summable_norm n h a ha t
  unfold infiniteGrid superpositionLift
  rw [← hs.sum_add_tsum_subtype_compl (band M), add_sub_cancel_left]
  have hb := norm_tsum_le_tsum_norm (hn.subtype (fun m => m ∉ band M))
  calc
    _ ≤ Real.sqrt h * (∑' m : {m : ℤ // m ∉ band M},
        ‖modeLiftCLM n h m (modeOrbit m t (a m))‖) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = ∑' m : {m : ℤ // m ∉ band M},
        Real.sqrt (2*Real.pi)*‖a m‖ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      simpa using modeLift_weighted_norm n h m hh.le hmesh (modeOrbit m t (a m))
    _ = _ := by rw [tsum_mul_left, ← tail_eq_tsum_compl M a ha]

end NDEAEvolve.Exp009


-- SOURCE lean/WeightedTail.lean SHA256 59fe3f191091a88679160d4fa1cd40f419582b6540363203b7cba0c4c2614b98

/-! A weighted absolutely summable coefficient moment gives a quantitative
Fourier tail estimate. The exponent is a natural number. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp009

def frequencyWeight (r : ℕ) (m : ℤ) : ℝ := (1 + |(m : ℝ)|)^r
def moment (r : ℕ) (a : ℤ → E 2) : ℝ :=
  ∑' m, frequencyWeight r m * ‖a m‖

theorem frequencyWeight_one_le (r : ℕ) (m : ℤ) : 1 ≤ frequencyWeight r m := by
  exact one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])

theorem frequencyWeight_nonneg (r : ℕ) (m : ℤ) : 0 ≤ frequencyWeight r m :=
  le_trans (by norm_num) (frequencyWeight_one_le r m)

theorem moment_nonneg (r : ℕ) (a : ℤ → E 2) : 0 ≤ moment r a :=
  tsum_nonneg fun m => mul_nonneg (frequencyWeight_nonneg r m) (norm_nonneg _)

theorem weighted_summable_implies_absolute (r : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    Summable fun m => ‖a m‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ha
  intro m
  exact le_mul_of_one_le_left (norm_nonneg _) (frequencyWeight_one_le r m)

theorem mass_le_moment (r : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    mass a ≤ moment r a := by
  apply (weighted_summable_implies_absolute r a ha).tsum_le_tsum _ ha
  intro m
  exact le_mul_of_one_le_left (norm_nonneg _) (frequencyWeight_one_le r m)

theorem outside_band_weight (r M : ℕ) (m : ℤ) (hm : m ∉ band M) :
    ((M : ℝ)+1)^r ≤ frequencyWeight r m := by
  have hab : (M : ℤ) < |m| := by
    by_contra hn
    have hp := abs_le.mp (le_of_not_gt hn)
    exact hm (Finset.mem_Icc.mpr hp)
  have habr : (M : ℝ) < |(m : ℝ)| := by exact_mod_cast hab
  unfold frequencyWeight
  apply pow_le_pow_left₀ (by positivity)
  linarith

theorem weighted_tail_bound (r M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    ((M : ℝ)+1)^r * tail M a ≤ moment r a := by
  have habs := weighted_summable_implies_absolute r a ha
  rw [tail_eq_tsum_compl M a habs, ← tsum_mul_left]
  have hfirst :
      (∑' m : {m : ℤ // m ∉ band M}, ((M : ℝ)+1)^r*‖a m‖) ≤
      ∑' m : {m : ℤ // m ∉ band M}, frequencyWeight r m * ‖a m‖ := by
    apply ((habs.subtype _).mul_left _).tsum_le_tsum _ (ha.subtype _)
    intro m
    exact mul_le_mul_of_nonneg_right (outside_band_weight r M m m.property) (norm_nonneg _)
  apply hfirst.trans
  have hparts := ha.sum_add_tsum_subtype_compl (band M)
  have hsum : 0 ≤ ∑ m ∈ band M, frequencyWeight r m * ‖a m‖ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (frequencyWeight_nonneg r m) (norm_nonneg _)
  unfold moment
  linarith

theorem tail_le_moment_div (r M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    tail M a ≤ moment r a / ((M : ℝ)+1)^r := by
  apply (le_div_iff₀ (by positivity : 0 < ((M : ℝ)+1)^r)).mpr
  simpa only [mul_comm] using weighted_tail_bound r M a ha

end NDEAEvolve.Exp009


-- SOURCE lean/CutoffSchedule.lean SHA256 41604c9d77be7780e933258a640deeacfbc3ddd0823aa2663667d1fc077be8f4

/-! A concrete growing Fourier cutoff and compatible space/time refinement. -/
noncomputable section
open Filter
open NDEAEvolve.Exp008
namespace NDEAEvolve.Exp009

set_option maxHeartbeats 100000

def cutoff (q : ℕ) : ℕ := q+1
def gridPoints (q : ℕ) : ℕ := 8*(cutoff q)^3
def gridIndex (q : ℕ) : ℕ := gridPoints q-1
def mesh (q : ℕ) : ℝ := 2*Real.pi/(gridPoints q:ℝ)
def timeStep (q : ℕ) : ℝ := 1/(6*(cutoff q:ℝ)^4)
def stepCount (q : ℕ) : ℕ := 6*(cutoff q)^4

theorem cutoff_pos (q : ℕ) : 1 ≤ cutoff q := by simp [cutoff]

theorem cutoff_real_ge_one (q : ℕ) : 1 ≤ (cutoff q:ℝ) := by
  exact_mod_cast cutoff_pos q

theorem gridPoints_pos (q : ℕ) : 0 < gridPoints q := by
  have := cutoff_pos q
  unfold gridPoints
  positivity

theorem gridPoints_eq_gridIndex_succ (q : ℕ) : gridPoints q=gridIndex q+1 := by
  have := gridPoints_pos q
  unfold gridIndex
  omega

theorem cutoff_unaliased (q : ℕ) : 2*cutoff q<gridIndex q+1 := by
  rw [← gridPoints_eq_gridIndex_succ]
  have hm := cutoff_pos q
  have hc : cutoff q ≤ (cutoff q)^3 := le_self_pow₀ hm (by decide)
  unfold gridPoints
  omega

theorem mesh_pos (q : ℕ) : 0 < mesh q := by
  have hp : 0 < (gridPoints q:ℝ) := by exact_mod_cast gridPoints_pos q
  unfold mesh
  positivity

theorem mesh_period (q : ℕ) : ((gridIndex q+1:ℕ):ℝ)*mesh q=2*Real.pi := by
  rw [← gridPoints_eq_gridIndex_succ]
  unfold mesh
  have hp : (gridPoints q:ℝ) ≠ 0 := by exact_mod_cast (gridPoints_pos q).ne'
  field_simp

theorem cutoff_mesh_le_one (q : ℕ) : (cutoff q:ℝ)*mesh q ≤ 1 := by
  have hm := cutoff_real_ge_one q
  have hc : (cutoff q:ℝ) ≤ (cutoff q:ℝ)^3 := le_self_pow₀ hm (by decide)
  have hp : 0 < (8:ℝ)*(cutoff q:ℝ)^3 := by positivity
  simp only [mesh, gridPoints, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hp).2
  have hpi := mul_le_mul_of_nonneg_left Real.pi_le_four (by positivity : 0 ≤ 2*(cutoff q:ℝ))
  linarith only [hpi, hc]

theorem timeStep_pos (q : ℕ) : 0 < timeStep q := by
  have := cutoff_real_ge_one q
  unfold timeStep
  positivity

theorem timeStep_nonneg (q : ℕ) : 0 ≤ timeStep q := (timeStep_pos q).le

theorem timeStep_restriction (q : ℕ) :
    2*timeStep q*((cutoff q:ℝ)^2+2) ≤ 1 := by
  have hm := cutoff_real_ge_one q
  have hsq : 1 ≤ (cutoff q:ℝ)^2 := one_le_pow₀ hm
  have hfour : (cutoff q:ℝ)^2 ≤ (cutoff q:ℝ)^4 := pow_le_pow_right₀ hm (by decide)
  have hp : 0 < (6:ℝ)*(cutoff q:ℝ)^4 := by positivity
  change 2*(1/(6*(cutoff q:ℝ)^4))*((cutoff q:ℝ)^2+2) ≤ 1
  rw [mul_one_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).2
  linarith only [hsq, hfour]

theorem stepCount_timeStep (q : ℕ) : (stepCount q:ℝ)*timeStep q=1 := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  simp only [stepCount, timeStep, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp

theorem cutoff_tendsto_atTop : Tendsto cutoff atTop atTop := tendsto_add_atTop_nat 1

theorem cutoff_inverse_tendsto_zero :
    Tendsto (fun q => (cutoff q:ℝ)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_nhds_zero_nat.comp cutoff_tendsto_atTop

theorem mesh_eq_inverse (q : ℕ) :
    mesh q = (Real.pi/4)*((cutoff q:ℝ)⁻¹)^3 := by
  simp only [mesh, gridPoints, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem timeStep_eq_inverse (q : ℕ) :
    timeStep q = (1/6:ℝ)*((cutoff q:ℝ)⁻¹)^4 := by
  unfold timeStep
  ring

theorem mesh_tendsto_zero : Tendsto mesh atTop (nhds 0) := by
  have h := (cutoff_inverse_tendsto_zero.pow 3).const_mul (Real.pi/4)
  simpa only [← mesh_eq_inverse, zero_pow (by omega : 3 ≠ 0), mul_zero] using h

theorem timeStep_tendsto_zero : Tendsto timeStep atTop (nhds 0) := by
  have h := (cutoff_inverse_tendsto_zero.pow 4).const_mul (1/6:ℝ)
  simpa only [← timeStep_eq_inverse, zero_pow (by omega : 4 ≠ 0), mul_zero] using h

theorem cutoff_error_eq_inverse (q : ℕ) :
    Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2 =
      ((1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128)*
        ((cutoff q:ℝ)⁻¹)^2 := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  rw [mesh_eq_inverse, timeStep_eq_inverse]
  unfold Ct Cs
  field_simp
  ring

theorem cutoff_error_tendsto_zero :
    Tendsto (fun q => Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)
      atTop (nhds 0) := by
  have hz := cutoff_inverse_tendsto_zero.pow 2
  have ha := (((tendsto_const_nhds (x := (1:ℝ))).add (hz.const_mul 2)).pow 3).const_mul (1000/36:ℝ)
  have hb := (ha.add_const (Real.pi^2/128)).mul hz
  simpa only [← cutoff_error_eq_inverse, zero_pow (by omega : 2 ≠ 0), mul_zero] using hb

/- Exact controls: the cutoff really grows, and the first schedule is admissible. -/
theorem control_cutoff_strict (q : ℕ) : cutoff q<cutoff (q+1) := by simp [cutoff]

theorem control_first_schedule :
    cutoff 0=1 ∧ gridPoints 0=8 ∧ gridIndex 0=7 ∧ stepCount 0=6 ∧ timeStep 0=1/6 := by
  norm_num [cutoff, gridPoints, gridIndex, stepCount, timeStep]


end NDEAEvolve.Exp009


-- SOURCE lean/InfiniteClosure.lean SHA256 bf99f2e9c96eac54902366b7e416b1a4c7bdbb6461f0c13226858ce70b9a0272

/-! Actual full-grid error against an absolutely summable infinite Fourier reference. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009

def infiniteGridError (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial -
    infiniteGrid n h a ((N:ℝ)*k)‖

def infiniteInitialError (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial - infiniteGrid n h a 0‖

theorem infiniteGridError_nonneg (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : 0 ≤ infiniteGridError n h k N a initial := by
  unfold infiniteGridError
  positivity

theorem infiniteInitialError_nonneg (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : 0 ≤ infiniteInitialError n h a initial := by
  unfold infiniteInitialError
  positivity

theorem infinite_exact_initial_error (n : ℕ) (h : ℝ) (a : ℤ → E 2) :
    infiniteInitialError n h a (infiniteGrid n h a 0) = 0 := by
  simp [infiniteInitialError]

theorem zero_steps_retain_full_initial_error (n : ℕ) (h k : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) :
    infiniteGridError n h k 0 a initial = infiniteInitialError n h a initial := by
  simp [infiniteGridError, infiniteInitialError]

theorem finite_initial_error_le_full (M n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) (ha : Summable fun m => ‖a m‖)
    (hh : 0 < h) (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    finiteInitialError n h (band M) a initial ≤
      infiniteInitialError n h a initial + Real.sqrt (2*Real.pi)*tail M a := by
  have hb := infiniteGrid_tail_bound M n h a 0 ha hh hmesh
  simp only [modeOrbit_initial] at hb
  have ht := mul_le_mul_of_nonneg_left
    (norm_sub_le_norm_sub_add_norm_sub initial (infiniteGrid n h a 0)
      (superpositionLift n h (band M) a)) (Real.sqrt_nonneg h)
  rw [mul_add] at ht
  exact ht.trans (add_le_add (le_refl _) hb)

theorem infinite_grid_error_bound (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) (ha : Summable fun m => ‖a m‖)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    infiniteGridError n h k N a initial ≤ infiniteInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a + 2*tail M a) := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  have hcost : 0 ≤ Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2) := by
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hT)
    exact add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
      (mul_nonneg (Cs_nonneg M) (sq_nonneg h))
  have ht := mul_le_mul_of_nonneg_left
    (norm_sub_le_norm_sub_add_norm_sub
      ((symmetric n h k Exp007.Z Exp007.X ^ N) initial)
      (superpositionLift n h (band M) (fun m => modeOrbit m ((N:ℝ)*k) (a m)))
      (infiniteGrid n h a ((N:ℝ)*k))) (Real.sqrt_nonneg h)
  rw [mul_add, norm_sub_rev (superpositionLift _ _ _ _)] at ht
  have htail := infiniteGrid_tail_bound M n h a ((N:ℝ)*k) ha hh hmesh
  have hfinite := finite_superposition_grid_error M n h k T N (band M) a initial
    hM hband (band_frequency_bound M) hmesh hh hMh hk hstep horizon
  have hi := finite_initial_error_le_full M n h a initial ha hh hmesh
  have hc := mul_le_mul_of_nonneg_left (coefficientNorm_band_le_mass M a ha) hcost
  change infiniteGridError n h k N a initial ≤ _ at ht
  change Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm (band M) a ≤
    Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*mass a at hc
  calc
    _ ≤ finiteGridError n h k N (band M) a initial +
        Real.sqrt (2*Real.pi)*tail M a := ht.trans (add_le_add (le_refl _) htail)
    _ ≤ (infiniteInitialError n h a initial + Real.sqrt (2*Real.pi)*tail M a) +
        Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*mass a +
        Real.sqrt (2*Real.pi)*tail M a :=
      add_le_add (hfinite.trans (add_le_add hi hc)) (le_refl _)
    _ = _ := by ring

theorem infinite_mesh_error_tendsto_zero
    (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖)
    (M n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hM : ∀ q, 1≤M q) (hband : ∀ q, 2*M q<n q+1)
    (hmesh : ∀ q, ((n q+1:ℕ):ℝ)*h q=2*Real.pi)
    (hh : ∀ q, 0<h q) (hMh : ∀ q, (M q:ℝ)*h q≤1)
    (hk : ∀ q, 0≤k q) (hstep : ∀ q, 2*k q*((M q:ℝ)^2+2)≤1)
    (horizon : ∀ q, (N q:ℝ)*k q≤T)
    (hM_limit : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hcost_limit : Filter.Tendsto (fun q => Ct (M q)*(k q)^2+Cs (M q)*(h q)^2)
      Filter.atTop (nhds 0))
    (hi_limit : Filter.Tendsto (fun q => infiniteInitialError (n q) (h q) a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => infiniteGridError (n q) (h q) (k q) (N q) a (initial q))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => infiniteGridError_nonneg _ _ _ _ _ _)
  · intro q
    exact infinite_grid_error_bound (M q) (n q) (h q) (k q) T (N q) a (initial q) ha
      (hM q) (hband q) (hmesh q) (hh q) (hMh q) (hk q) (hstep q) (horizon q)
  · have htail := (tail_tendsto_zero a ha).comp hM_limit
    have hb := hi_limit.add
      ((((hcost_limit.const_mul T).mul_const (mass a)).add (htail.const_mul 2)).const_mul
        (Real.sqrt (2*Real.pi)))
    simpa using hb

end NDEAEvolve.Exp009


-- SOURCE lean/WeightedClosure.lean SHA256 98df998a9a953fa4bdc58cd15dc3e1731a86180a0938933a81487f4568e7a970

/-! Quantitative full-reference error under a weighted coefficient moment. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp009

theorem weighted_infinite_grid_error_bound (r M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n))
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    infiniteGridError n h k N a initial ≤ infiniteInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a +
        2*(moment r a / ((M:ℝ)+1)^r)) := by
  apply (infinite_grid_error_bound M n h k T N a initial
    (weighted_summable_implies_absolute r a ha) hM hband hmesh hh hMh hk hstep horizon).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (tail_le_moment_div r M a ha)
      (by norm_num : (0:ℝ)≤2))) (Real.sqrt_nonneg _))

end NDEAEvolve.Exp009


-- SOURCE lean/ScheduleClosure.lean SHA256 d11f50dace8452e6b42558b378d98b23578853e21b3598a399f6bba981cffc5f

/-! Non-vacuous convergence to the full Fourier evolution at terminal time one. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp009

theorem scheduled_infinite_grid_error (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) (ha : Summable fun m => ‖a m‖) :
    infiniteGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial ≤
      infiniteInitialError (gridIndex q) (mesh q) a initial + Real.sqrt (2*Real.pi)*
        ((Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)*mass a +
          2*tail (cutoff q) a) := by
  simpa only [one_mul] using infinite_grid_error_bound (cutoff q) (gridIndex q)
    (mesh q) (timeStep q) 1 (stepCount q) a initial ha (cutoff_pos q)
    (cutoff_unaliased q) (mesh_period q) (mesh_pos q) (cutoff_mesh_le_one q)
    (timeStep_nonneg q) (timeStep_restriction q) (stepCount_timeStep q).le

theorem scheduled_infinite_error_tendsto_zero (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖)
    (initial : (q : ℕ) → Vec (Grid (gridIndex q)))
    (hi : Filter.Tendsto (fun q => infiniteInitialError (gridIndex q) (mesh q) a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => infiniteGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (initial q)) Filter.atTop (nhds 0) :=
  infinite_mesh_error_tendsto_zero a ha cutoff gridIndex stepCount mesh timeStep 1 initial
    cutoff_pos cutoff_unaliased mesh_period mesh_pos cutoff_mesh_le_one timeStep_nonneg
    timeStep_restriction (fun q => (stepCount_timeStep q).le) cutoff_tendsto_atTop
    cutoff_error_tendsto_zero hi

theorem scheduled_exact_initial_error_tendsto_zero (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    Filter.Tendsto (fun q => infiniteGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (infiniteGrid (gridIndex q) (mesh q) a 0))
      Filter.atTop (nhds 0) := by
  apply scheduled_infinite_error_tendsto_zero a ha
  simpa only [infinite_exact_initial_error] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds 0))

theorem scheduled_reference_time_one (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) :
    infiniteGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial =
      Real.sqrt (mesh q)*‖(symmetric (gridIndex q) (mesh q) (timeStep q)
        Exp007.Z Exp007.X ^ stepCount q) initial - infiniteGrid (gridIndex q) (mesh q) a 1‖ := by
  unfold infiniteGridError
  rw [stepCount_timeStep]

end NDEAEvolve.Exp009


-- SOURCE lean/Controls.lean SHA256 1bd7122751b4ba8ceb36a55e3d66bba7b552959ab631d4d0d7e73f9d7a2bce54

/-! Exact controls with a coefficient at every signed integer frequency.
The encoded geometric sequence is an independent formal example, not the
two-spinor geometric datum used by the floating-point diagnostic. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009.Controls

def geometricCoefficients (m : ℤ) : E 2 :=
  ((1/2 : ℂ)^Encodable.encode m) • Exp007.Controls.initialSpinor

theorem geometric_coefficient_norm (m : ℤ) :
    ‖geometricCoefficients m‖ = (1/2 : ℝ)^Encodable.encode m := by
  simp [geometricCoefficients, norm_smul, norm_pow, Exp007.Controls.initialSpinor_norm]

theorem geometric_summable_norm : Summable (fun m : ℤ => ‖geometricCoefficients m‖) := by
  simp only [geometric_coefficient_norm]
  exact summable_geometric_two_encode

theorem geometric_coefficient_nonzero (m : ℤ) : geometricCoefficients m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [geometric_coefficient_norm]
  positivity

theorem geometric_support_all : Function.support geometricCoefficients = Set.univ := by
  ext m
  simp [Function.mem_support, geometric_coefficient_nonzero]

theorem geometric_infinite_support : (Function.support geometricCoefficients).Infinite := by
  rw [geometric_support_all]
  exact Set.infinite_univ

theorem geometric_tail_positive (M : ℕ) : 0 < tail M geometricCoefficients := by
  have hm : (M:ℤ)+1 ∉ band M := by simp [band]
  let j : {m : ℤ // m ∉ band M} := ⟨(M:ℤ)+1, hm⟩
  rw [tail_eq_tsum_compl M geometricCoefficients geometric_summable_norm]
  have hs := geometric_summable_norm.subtype (fun m => m ∉ band M)
  have hp : 0 < ‖geometricCoefficients j‖ := norm_pos_iff.mpr (geometric_coefficient_nonzero _)
  exact hp.trans_le (hs.le_tsum j (fun _ _ => norm_nonneg _))

theorem geometric_tail_tends_to_zero :
    Filter.Tendsto (fun M => tail M geometricCoefficients) Filter.atTop (nhds 0) :=
  tail_tendsto_zero geometricCoefficients geometric_summable_norm

theorem geometric_infinite_reference_summable (t x : ℝ) :
    Summable (fun m => Exp008.modeSolution m (geometricCoefficients m) t x) :=
  modeSolution_summable geometricCoefficients geometric_summable_norm t x

theorem grid_multiple_is_constant_mode (n r : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (v : E 2) :
    modeLift n h ((r*(n+1):ℕ):ℤ) v = modeLift n h 0 v := by
  ext p
  simp only [modeLift, WithLp.ofLp_toLp, Int.cast_natCast, Int.cast_zero]
  have hp : Exp006.phase (((r*(n+1):ℕ):ℝ)*((p.1.val:ℝ)*h))=1 := by
    rw [show ((r*(n+1):ℕ):ℝ)*((p.1.val:ℝ)*h) =
      ((r*p.1.val:ℕ):ℝ)*(((n+1:ℕ):ℝ)*h) by push_cast; ring, hmesh]
    simpa using Exp006.phase_periodic.nat_mul_eq (r*p.1.val)
  rw [hp]
  simp

/-- Coherent modes at d and 2d have more sampled energy than the naive l2
formula. Both frequencies are outside every cutoff M<d. -/
theorem coherent_aliases_violate_l2_sampling (n : ℕ) (h : ℝ)
    (hh : 0<h) (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    2*Real.pi*(‖Exp007.Controls.initialSpinor‖^2+‖Exp007.Controls.initialSpinor‖^2) <
      (Real.sqrt h*‖modeLift n h ((1*(n+1):ℕ):ℤ) Exp007.Controls.initialSpinor +
        modeLift n h ((2*(n+1):ℕ):ℤ) Exp007.Controls.initialSpinor‖)^2 := by
  rw [grid_multiple_is_constant_mode n 1 h hmesh,
    grid_multiple_is_constant_mode n 2 h hmesh]
  have hn : ‖modeLift n h 0 Exp007.Controls.initialSpinor +
      modeLift n h 0 Exp007.Controls.initialSpinor‖ =
      2*‖modeLift n h 0 Exp007.Controls.initialSpinor‖ := by
    rw [← two_smul ℂ (modeLift n h 0 Exp007.Controls.initialSpinor), norm_smul]
    norm_num
  have hw := modeLift_weighted_norm n h 0 hh.le hmesh Exp007.Controls.initialSpinor
  rw [Exp007.Controls.initialSpinor_norm, mul_one] at hw
  rw [hn]
  rw [show Real.sqrt h*(2*‖modeLift n h 0 Exp007.Controls.initialSpinor‖) =
    2*(Real.sqrt h*‖modeLift n h 0 Exp007.Controls.initialSpinor‖) by ring, hw]
  rw [Exp007.Controls.initialSpinor_norm]
  nlinarith [Real.sq_sqrt (by positivity : 0≤2*Real.pi), Real.pi_pos]

end NDEAEvolve.Exp009.Controls




-- SOURCE lean/Regularity.lean SHA256 e219924f02855f9d2abc2303b56e791a7f6cb7224779736200a4881719e59299

/-! A summable second weighted Fourier moment bounds every derivative needed
for the classical periodic spinor equation. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
namespace NDEAEvolve.Exp010

def Regular (a : ℤ → E 2) : Prop :=
  Summable fun m => frequencyWeight 2 m * ‖a m‖

def modeTime (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (-Complex.I) • operatorOf (modeGenerator m) (modeSolution m v t x)

def modeSpace (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (Complex.I*(m:ℂ)) • modeSolution m v t x

def modeSecond (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (-((m:ℂ)^2)) • modeSolution m v t x

theorem regular_absolute (a : ℤ → E 2) (ha : Regular a) :
    Summable fun m => ‖a m‖ := weighted_summable_implies_absolute 2 a ha

theorem frequencyWeight_two_pos (m : ℤ) : 0 < frequencyWeight 2 m :=
  lt_of_lt_of_le (by norm_num) (frequencyWeight_one_le 2 m)

theorem frequency_abs_le_weight (m : ℤ) : |(m:ℝ)| ≤ frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_nonneg |(m:ℝ)|]

theorem frequency_sq_le_weight (m : ℤ) : (m:ℝ)^2 ≤ frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_abs (m:ℝ)]

theorem frequency_generator_le_weight (m : ℤ) :
    (m:ℝ)^2+2 ≤ 2*frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_abs (m:ℝ), sq_nonneg (m:ℝ)]

theorem modeGenerator_norm_le (m : ℤ) : ‖operatorOf (modeGenerator m)‖ ≤ (m:ℝ)^2+2 := by
  calc
    _ ≤ ‖operatorOf (Exp007.A ((m:ℝ)^2))‖+‖operatorOf Exp007.B‖ := by
      simpa only [modeGenerator, operatorOf, map_add] using
        norm_add_le (operatorOf (Exp007.A ((m:ℝ)^2))) (operatorOf Exp007.B)
    _ ≤ ((m:ℝ)^2+1)+1 := add_le_add
      (A_opNorm_le ((m:ℝ)^2) (sq_nonneg _)) Exp007.B_opNorm_le_one
    _ = _ := by ring

theorem complex_integer_norm (m : ℤ) : ‖(m:ℂ)‖ = |(m:ℝ)| := by
  have he : (m:ℂ)=((m:ℝ):ℂ) := by simp
  rw [he, Complex.norm_real, Real.norm_eq_abs]

theorem modeTime_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeTime m v t x‖ ≤ 2*frequencyWeight 2 m*‖v‖ := by
  unfold modeTime
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖operatorOf (modeGenerator m)‖*‖modeSolution m v t x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((m:ℝ)^2+2)*‖v‖ := by
      rw [modeSolution_norm]
      exact mul_le_mul_of_nonneg_right (modeGenerator_norm_le m) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (frequency_generator_le_weight m) (norm_nonneg _)

theorem modeSpace_norm_eq (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSpace m v t x‖ = |(m:ℝ)| * ‖v‖ := by
  simp only [modeSpace, norm_smul, norm_mul, Complex.norm_I, one_mul,
    complex_integer_norm, modeSolution_norm]

theorem modeSecond_norm_eq (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSecond m v t x‖ = (m:ℝ)^2*‖v‖ := by
  simp only [modeSecond, norm_smul, norm_neg, norm_pow, complex_integer_norm,
    sq_abs, modeSolution_norm]

theorem modeSpace_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSpace m v t x‖ ≤ frequencyWeight 2 m*‖v‖ := by
  rw [modeSpace_norm_eq]
  exact mul_le_mul_of_nonneg_right (frequency_abs_le_weight m) (norm_nonneg _)

theorem modeSecond_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSecond m v t x‖ ≤ frequencyWeight 2 m*‖v‖ := by
  rw [modeSecond_norm_eq]
  exact mul_le_mul_of_nonneg_right (frequency_sq_le_weight m) (norm_nonneg _)

theorem regular_time_majorant (a : ℤ → E 2) (ha : Regular a) :
    Summable fun m => 2*frequencyWeight 2 m*‖a m‖ := by
  simpa only [mul_assoc] using ha.mul_left 2

theorem regular_time_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeTime m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeTime_norm_le m (a m) t x) (regular_time_majorant a ha)

theorem regular_space_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeSpace m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeSpace_norm_le m (a m) t x) ha

theorem regular_second_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeSecond m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeSecond_norm_le m (a m) t x) ha

theorem regular_time_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeTime m (a m) t x := (regular_time_summable_norm a ha t x).of_norm

theorem regular_space_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeSpace m (a m) t x := (regular_space_summable_norm a ha t x).of_norm

theorem regular_second_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeSecond m (a m) t x := (regular_second_summable_norm a ha t x).of_norm

end NDEAEvolve.Exp010


-- SOURCE lean/ClassicalSolution.lean SHA256 6ec534b1c1413569f16e166fb3f3b68c15a3c83791748a68f10607d83390ed51

/-! Actual derivatives of the infinite Fourier solution. The second weighted
coefficient moment supplies summable bounds uniform in time and position, so
the three exchanges of derivative and infinite sum are proved here. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
namespace NDEAEvolve.Exp010

theorem mode_time_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (fun s => modeSolution m v s x) (modeTime m v t x) t := by
  simpa [modeTime, modeSolution, map_smul, smul_smul, mul_comm] using
    modeSolution_time_hasDerivAt m v t x

theorem mode_space_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSolution m v t) (modeSpace m v t x) x := by
  simpa [modeSpace, modeSolution, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    modeSolution_space_hasDerivAt m v t x

theorem mode_second_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSpace m v t) (modeSecond m v t x) x := by
  have h : modeSpace m v t = deriv (modeSolution m v t) :=
    funext fun y => (mode_space_hasDerivAt m v t y).deriv.symm
  rw [h]
  exact modeSolution_second_hasDerivAt m v t x

theorem mode_schrodinger (m : ℤ) (v : E 2) (t x : ℝ) :
    Complex.I • modeTime m v t x =
      -modeSecond m v t x + operatorOf (Exp007.Z + Exp007.X) (modeSolution m v t x) := by
  rw [← (mode_time_hasDerivAt m v t x).deriv]
  simpa [modeSecond, modeSolution_second_derivative] using modeSolution_schrodinger m v t x

theorem infiniteSolution_time_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (fun s => Exp009.infiniteSolution a s x)
      (∑' m, modeTime m (a m) t x) t := by
  exact hasDerivAt_tsum (regular_time_majorant a ha)
    (fun m s => mode_time_hasDerivAt m (a m) s x)
    (fun m s => modeTime_norm_le m (a m) s x)
    (Exp009.modeSolution_summable a (regular_absolute a ha) 0 x) t

theorem infiniteSolution_space_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (Exp009.infiniteSolution a t)
      (∑' m, modeSpace m (a m) t x) x := by
  exact hasDerivAt_tsum ha
    (fun m y => mode_space_hasDerivAt m (a m) t y)
    (fun m y => modeSpace_norm_le m (a m) t y)
    (Exp009.modeSolution_summable a (regular_absolute a ha) t 0) x

theorem infiniteSolution_time_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (fun s => Exp009.infiniteSolution a s x) t = ∑' m, modeTime m (a m) t x :=
  (infiniteSolution_time_hasDerivAt a ha t x).deriv

theorem infiniteSolution_space_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (Exp009.infiniteSolution a t) x = ∑' m, modeSpace m (a m) t x :=
  (infiniteSolution_space_hasDerivAt a ha t x).deriv

theorem infiniteSolution_second_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (deriv (Exp009.infiniteSolution a t))
      (∑' m, modeSecond m (a m) t x) x := by
  have he : deriv (Exp009.infiniteSolution a t) =
      fun y => ∑' m, modeSpace m (a m) t y :=
    funext (infiniteSolution_space_derivative a ha t)
  rw [he]
  exact hasDerivAt_tsum ha
    (fun m y => mode_second_hasDerivAt m (a m) t y)
    (fun m y => modeSecond_norm_le m (a m) t y)
    (regular_space_summable a ha t 0) x

theorem infiniteSolution_second_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (deriv (Exp009.infiniteSolution a t)) x = ∑' m, modeSecond m (a m) t x :=
  (infiniteSolution_second_hasDerivAt a ha t x).deriv

/-- The infinite series solves the spinor Schrödinger equation in actual real
time and space derivatives, with the same noncommuting split potential as the
finite-band predecessor. -/
theorem infiniteSolution_schrodinger (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Complex.I • deriv (fun s => Exp009.infiniteSolution a s x) t =
      -deriv (deriv (Exp009.infiniteSolution a t)) x +
        operatorOf (Exp007.Z + Exp007.X) (Exp009.infiniteSolution a t x) := by
  rw [infiniteSolution_time_derivative a ha t x,
    infiniteSolution_second_derivative a ha t x]
  have hu := Exp009.modeSolution_summable a (regular_absolute a ha) t x
  have ht := regular_time_summable a ha t x
  have hxx := regular_second_summable a ha t x
  have hv := hu.mapL (operatorOf (Exp007.Z + Exp007.X))
  rw [← ht.tsum_const_smul Complex.I, ← tsum_neg,
    Exp009.infiniteSolution, (operatorOf (Exp007.Z + Exp007.X)).map_tsum hu,
    ← hxx.neg.tsum_add hv]
  exact tsum_congr fun m => mode_schrodinger m (a m) t x

end NDEAEvolve.Exp010


-- SOURCE lean/Continuity.lean SHA256 7e26cbb8653f1a1d8926674a3f9e4d2ebfc60abfd49eb2a7b4fa0dc8984a63a6

/-! Joint continuity of the solution and its actual classical derivatives.
The global second-moment majorant covers the entire time-space plane. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
namespace NDEAEvolve.Exp010

theorem modeSolution_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSolution m v p.1 p.2) := by
  have ht : Continuous (fun t : ℝ => modeOrbit m t v) :=
    continuous_iff_continuousAt.mpr fun t => (modeOrbit_hasDerivAt m v t).continuousAt
  have hx : Continuous (fun x : ℝ => Exp006.phase ((m : ℝ) * x)) :=
    continuous_iff_continuousAt.mpr fun x => (phaseMode_hasDerivAt m x).continuousAt
  exact (hx.comp continuous_snd).smul (ht.comp continuous_fst)

theorem modeTime_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeTime m v p.1 p.2) := by
  exact ((operatorOf (modeGenerator m)).continuous.comp
    (modeSolution_continuous m v)).const_smul (-Complex.I)

theorem modeSpace_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSpace m v p.1 p.2) :=
  (modeSolution_continuous m v).const_smul (Complex.I * (m : ℂ))

theorem modeSecond_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSecond m v p.1 p.2) :=
  (modeSolution_continuous m v).const_smul (-((m : ℂ)^2))

/-- Absolute summability alone already gives joint continuity of the solution. -/
theorem infiniteSolution_continuous_of_absolute (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    Continuous (fun p : ℝ × ℝ => Exp009.infiniteSolution a p.1 p.2) := by
  exact continuous_tsum (fun m => modeSolution_continuous m (a m)) ha
    (fun m p => le_of_eq (modeSolution_norm m (a m) p.1 p.2))

theorem infiniteSolution_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => Exp009.infiniteSolution a p.1 p.2) :=
  infiniteSolution_continuous_of_absolute a (regular_absolute a ha)

theorem infiniteSolution_time_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => Exp009.infiniteSolution a s p.2) p.1) := by
  have he : (fun p : ℝ × ℝ => deriv (fun s => Exp009.infiniteSolution a s p.2) p.1) =
      fun p => ∑' m, modeTime m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_time_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeTime_continuous m (a m))
    (regular_time_majorant a ha)
    (fun m p => modeTime_norm_le m (a m) p.1 p.2)

theorem infiniteSolution_space_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (Exp009.infiniteSolution a p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (Exp009.infiniteSolution a p.1) p.2) =
      fun p => ∑' m, modeSpace m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_space_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeSpace_continuous m (a m)) ha
    (fun m p => modeSpace_norm_le m (a m) p.1 p.2)

theorem infiniteSolution_second_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (Exp009.infiniteSolution a p.1)) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (deriv (Exp009.infiniteSolution a p.1)) p.2) =
      fun p => ∑' m, modeSecond m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_second_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeSecond_continuous m (a m)) ha
    (fun m p => modeSecond_norm_le m (a m) p.1 p.2)

/-- Classical periodic solution of the spinor equation. Derivative existence is
included explicitly because Lean's `deriv` is a totalized operation. -/
structure IsClassicalPeriodicSolution (u : ℝ → ℝ → E 2) : Prop where
  time_differentiable : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space_differentiable : ∀ t x, DifferentiableAt ℝ (u t) x
  second_space_differentiable : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x
  continuous_solution : Continuous (fun p : ℝ × ℝ => u p.1 p.2)
  continuous_time_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1)
  continuous_space_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)
  continuous_second_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (u p.1)) p.2)
  periodic : ∀ t, Function.Periodic (u t) (2 * Real.pi)
  schrodinger : ∀ t x, Complex.I • deriv (fun s => u s x) t =
    -deriv (deriv (u t)) x + operatorOf (Exp007.Z + Exp007.X) (u t x)

/-- A finite second weighted Fourier moment gives a classical periodic solution
with actual time and space derivatives and the pointwise PDE. -/
theorem infiniteSolution_classical (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (Exp009.infiniteSolution a) where
  time_differentiable t x := (infiniteSolution_time_hasDerivAt a ha t x).differentiableAt
  space_differentiable t x := (infiniteSolution_space_hasDerivAt a ha t x).differentiableAt
  second_space_differentiable t x :=
    (infiniteSolution_second_hasDerivAt a ha t x).differentiableAt
  continuous_solution := infiniteSolution_continuous a ha
  continuous_time_derivative := infiniteSolution_time_derivative_continuous a ha
  continuous_space_derivative := infiniteSolution_space_derivative_continuous a ha
  continuous_second_derivative := infiniteSolution_second_derivative_continuous a ha
  periodic := Exp009.infiniteSolution_periodic a
  schrodinger := infiniteSolution_schrodinger a ha

end NDEAEvolve.Exp010


-- SOURCE lean/ClassicalClosure.lean SHA256 0084bc521a7fd4db76668d1bce8b5a0267b263878040f8f30fe51c4757ca0745

/-! Actual numerical errors against pointwise samples of the classical PDE solution. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp010

def sampleSolution (n : ℕ) (h : ℝ) (u : ℝ → ℝ → E 2) (t : ℝ) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => u t ((p.1.val:ℝ)*h) p.2)

def classicalGridError (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial -
    sampleSolution n h (infiniteSolution a) ((N:ℝ)*k)‖

def classicalInitialError (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial - sampleSolution n h (infiniteSolution a) 0‖

theorem sampleSolution_eq_infiniteGrid (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Regular a) (t : ℝ) :
    sampleSolution n h (infiniteSolution a) t = infiniteGrid n h a t := by
  ext p
  exact (infiniteGrid_is_sampled_solution n h a (regular_absolute a ha) t p).symm

theorem classicalGridError_eq (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (ha : Regular a) (initial : Vec (Grid n)) :
    classicalGridError n h k N a initial = infiniteGridError n h k N a initial := by
  unfold classicalGridError infiniteGridError
  rw [sampleSolution_eq_infiniteGrid n h a ha]

theorem classicalInitialError_eq (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Regular a) (initial : Vec (Grid n)) :
    classicalInitialError n h a initial = infiniteInitialError n h a initial := by
  unfold classicalInitialError infiniteInitialError
  rw [sampleSolution_eq_infiniteGrid n h a ha]

theorem classical_grid_error_bound (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) (ha : Regular a)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    classicalGridError n h k N a initial ≤ classicalInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a +
        2*(moment 2 a / ((M:ℝ)+1)^2)) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  rw [classicalGridError_eq n h k N a ha, classicalInitialError_eq n h a ha]
  exact weighted_infinite_grid_error_bound 2 M n h k T N a initial ha
    hM hband hmesh hh hMh hk hstep horizon

theorem scheduled_classical_reference_time_one (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial =
      Real.sqrt (mesh q)*‖(symmetric (gridIndex q) (mesh q) (timeStep q)
        Exp007.Z Exp007.X ^ stepCount q) initial -
          sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 1‖ := by
  unfold classicalGridError
  rw [stepCount_timeStep]

theorem scheduled_classical_error_tendsto_zero (a : ℤ → E 2) (ha : Regular a)
    (initial : (q : ℕ) → Vec (Grid (gridIndex q)))
    (hi : Filter.Tendsto (fun q => classicalInitialError (gridIndex q) (mesh q) a (initial q))
      Filter.atTop (nhds 0)) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    Filter.Tendsto (fun q => classicalGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (initial q)) Filter.atTop (nhds 0) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  simp only [classicalInitialError_eq _ _ a ha] at hi
  simp only [classicalGridError_eq _ _ _ _ a ha]
  exact scheduled_infinite_error_tendsto_zero a (regular_absolute a ha) initial hi

theorem scheduled_classical_exact_initial_convergence (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    Filter.Tendsto (fun q => classicalGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0))
      Filter.atTop (nhds 0) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  simp only [classicalGridError_eq _ _ _ _ a ha, sampleSolution_eq_infiniteGrid _ _ a ha]
  exact scheduled_exact_initial_error_tendsto_zero a (regular_absolute a ha)

end NDEAEvolve.Exp010


-- SOURCE lean/Controls.lean SHA256 9c847094a530fd8626d30178338b849e33c0a053d0d14c1a7b988e836a504a20

/-! Exact nonvacuity controls for the second weighted coefficient moment.
The datum has a nonzero coefficient at every signed integer. Dividing the
encoded geometric coefficient by the exact weight makes its regularity
verification independent of any asymptotic relation between encode and |m|.
It differs from the signed geometric datum in the floating-point diagnostics. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp010.Controls

def regularGeometricCoefficients (m : ℤ) : E 2 :=
  ((1 / 2 : ℂ)^Encodable.encode m / (Exp009.frequencyWeight 2 m : ℂ)) •
    Exp007.Controls.initialSpinor

theorem regular_geometric_coefficient_norm (m : ℤ) :
    ‖regularGeometricCoefficients m‖ =
      (1 / 2 : ℝ)^Encodable.encode m / Exp009.frequencyWeight 2 m := by
  simp [regularGeometricCoefficients, norm_smul, norm_div, norm_pow,
    Exp007.Controls.initialSpinor_norm,
    Real.norm_eq_abs, abs_of_nonneg (Exp009.frequencyWeight_nonneg 2 m)]

theorem regular_geometric_weighted_norm (m : ℤ) :
    Exp009.frequencyWeight 2 m * ‖regularGeometricCoefficients m‖ =
      (1 / 2 : ℝ)^Encodable.encode m := by
  rw [regular_geometric_coefficient_norm]
  have hw : Exp009.frequencyWeight 2 m ≠ 0 := by
    have := Exp009.frequencyWeight_one_le 2 m
    linarith
  exact mul_div_cancel₀ _ hw

theorem regular_geometric_regular : Regular regularGeometricCoefficients := by
  change Summable (fun m : ℤ => Exp009.frequencyWeight 2 m *
    ‖regularGeometricCoefficients m‖)
  simp only [regular_geometric_weighted_norm]
  exact summable_geometric_two_encode

theorem regular_geometric_summable_norm :
    Summable (fun m : ℤ => ‖regularGeometricCoefficients m‖) :=
  Exp009.weighted_summable_implies_absolute 2 _ regular_geometric_regular

theorem regular_geometric_coefficient_nonzero (m : ℤ) :
    regularGeometricCoefficients m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [regular_geometric_coefficient_norm]
  have hw : 0 < Exp009.frequencyWeight 2 m := by
    have := Exp009.frequencyWeight_one_le 2 m
    linarith
  positivity

theorem regular_geometric_support_all :
    Function.support regularGeometricCoefficients = Set.univ := by
  ext m
  simp [Function.mem_support, regular_geometric_coefficient_nonzero]

theorem regular_geometric_infinite_support :
    (Function.support regularGeometricCoefficients).Infinite := by
  rw [regular_geometric_support_all]
  exact Set.infinite_univ

theorem regular_geometric_tail_positive (M : ℕ) :
    0 < Exp009.tail M regularGeometricCoefficients := by
  have hm : (M : ℤ) + 1 ∉ Exp009.band M := by simp [Exp009.band]
  let j : {m : ℤ // m ∉ Exp009.band M} := ⟨(M : ℤ) + 1, hm⟩
  rw [Exp009.tail_eq_tsum_compl M regularGeometricCoefficients
    regular_geometric_summable_norm]
  have hs := regular_geometric_summable_norm.subtype (fun m => m ∉ Exp009.band M)
  have hp : 0 < ‖regularGeometricCoefficients j‖ :=
    norm_pos_iff.mpr (regular_geometric_coefficient_nonzero _)
  exact hp.trans_le (hs.le_tsum j (fun _ _ => norm_nonneg _))

theorem zero_coefficients_regular : Regular (fun _ : ℤ => (0 : E 2)) := by
  change Summable (fun m : ℤ => Exp009.frequencyWeight 2 m * ‖(0 : E 2)‖)
  simp

theorem zero_infinite_solution (t x : ℝ) :
    Exp009.infiniteSolution (fun _ : ℤ => (0 : E 2)) t x = 0 := by
  simp [Exp009.infiniteSolution, Exp008.modeSolution, Exp008.modeOrbit]

def singleCoefficients (j : ℤ) (v : E 2) (m : ℤ) : E 2 :=
  if m = j then v else 0

theorem single_coefficients_regular (j : ℤ) (v : E 2) :
    Regular (singleCoefficients j v) := by
  have he : (fun m : ℤ => Exp009.frequencyWeight 2 m * ‖singleCoefficients j v m‖) =
      (fun m : ℤ => if m = j then Exp009.frequencyWeight 2 j * ‖v‖ else 0) := by
    funext m
    by_cases hm : m = j <;> simp [singleCoefficients, hm]
  change Summable _
  rw [he]
  exact (hasSum_ite_eq j (Exp009.frequencyWeight 2 j * ‖v‖)).summable

theorem single_infinite_solution (j : ℤ) (v : E 2) (t x : ℝ) :
    Exp009.infiniteSolution (singleCoefficients j v) t x =
      Exp008.modeSolution j v t x := by
  unfold Exp009.infiniteSolution
  rw [tsum_eq_single j]
  · simp [singleCoefficients]
  · intro m hm
    simp [singleCoefficients, hm, Exp008.modeSolution, Exp008.modeOrbit]

theorem negative_frequency_derivative_sign (v : E 2) :
    deriv (Exp009.infiniteSolution (singleCoefficients (-1) v) 0) 0 =
      (-Complex.I) • v := by
  have he : Exp009.infiniteSolution (singleCoefficients (-1) v) 0 =
      Exp008.modeSolution (-1) v 0 := funext fun x => single_infinite_solution (-1) v 0 x
  rw [he, (Exp008.modeSolution_space_hasDerivAt (-1) v 0 0).deriv]
  simp

theorem positive_frequency_derivative_sign (v : E 2) :
    deriv (Exp009.infiniteSolution (singleCoefficients 1 v) 0) 0 =
      Complex.I • v := by
  have he : Exp009.infiniteSolution (singleCoefficients 1 v) 0 =
      Exp008.modeSolution 1 v 0 := funext fun x => single_infinite_solution 1 v 0 x
  rw [he, (Exp008.modeSolution_space_hasDerivAt 1 v 0 0).deriv]
  simp

theorem negative_frequency_second_derivative_sign (v : E 2) :
    deriv (deriv (Exp009.infiniteSolution (singleCoefficients (-1) v) 0)) 0 = -v := by
  have he : Exp009.infiniteSolution (singleCoefficients (-1) v) 0 =
      Exp008.modeSolution (-1) v 0 := funext fun x => single_infinite_solution (-1) v 0 x
  rw [he, Exp008.modeSolution_second_derivative]
  simp

theorem regular_geometric_classical :
    IsClassicalPeriodicSolution (Exp009.infiniteSolution regularGeometricCoefficients) :=
  infiniteSolution_classical regularGeometricCoefficients regular_geometric_regular

theorem regular_geometric_schrodinger (t x : ℝ) :
    Complex.I • deriv (fun s => Exp009.infiniteSolution regularGeometricCoefficients s x) t =
      -deriv (deriv (Exp009.infiniteSolution regularGeometricCoefficients t)) x +
        operatorOf (Exp007.Z + Exp007.X)
          (Exp009.infiniteSolution regularGeometricCoefficients t x) :=
  infiniteSolution_schrodinger regularGeometricCoefficients regular_geometric_regular t x

theorem infinite_support_classical_example :
    ∃ a : ℤ → E 2, (∀ m, a m ≠ 0) ∧ Regular a ∧
      (Function.support a).Infinite ∧ IsClassicalPeriodicSolution (Exp009.infiniteSolution a) :=
  ⟨regularGeometricCoefficients, regular_geometric_coefficient_nonzero,
    regular_geometric_regular, regular_geometric_infinite_support, regular_geometric_classical⟩

end NDEAEvolve.Exp010.Controls




-- SOURCE lean/SolutionLipschitz.lean SHA256 01986d7ebcbce986000c404993621bf46b12d0fe0b18bf24b163de5fdddfcaf6

/-! Global time and space bounds for the actual classical Fourier solution.
The second weighted coefficient moment bounds the actual derivatives, and
the mean value inequality converts those bounds to pointwise differences. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

theorem derivative_space_norm_le (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    ‖deriv (infiniteSolution a t) x‖ ≤ moment 2 a := by
  rw [infiniteSolution_space_derivative a ha t x]
  exact (norm_tsum_le_tsum_norm (regular_space_summable_norm a ha t x)).trans
    ((regular_space_summable_norm a ha t x).tsum_le_tsum
      (fun m => modeSpace_norm_le m (a m) t x) ha)

theorem derivative_time_norm_le (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    ‖deriv (fun s => infiniteSolution a s x) t‖ ≤ 2 * moment 2 a := by
  rw [infiniteSolution_time_derivative a ha t x]
  calc
    _ ≤ ∑' m, ‖modeTime m (a m) t x‖ :=
      norm_tsum_le_tsum_norm (regular_time_summable_norm a ha t x)
    _ ≤ ∑' m, 2 * frequencyWeight 2 m * ‖a m‖ :=
      (regular_time_summable_norm a ha t x).tsum_le_tsum
        (fun m => modeTime_norm_le m (a m) t x) (regular_time_majorant a ha)
    _ = 2 * moment 2 a := by simp only [mul_assoc, tsum_mul_left, moment]

theorem solution_space_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t x y : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a t y‖ ≤ moment 2 a * |x - y| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun z _ => (infiniteSolution_space_hasDerivAt a ha t z).differentiableAt)
    (fun z _ => derivative_space_norm_le a ha t z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hb

theorem solution_time_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t s x : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s x‖ ≤ 2 * moment 2 a * |t - s| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun z _ => (infiniteSolution_time_hasDerivAt a ha z x).differentiableAt)
    (fun z _ => derivative_time_norm_le a ha z x) convex_univ
    (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hb

theorem solution_space_lipschitz (a : ℤ → E 2) (ha : Regular a) (t x y : ℝ) :
    ‖infiniteSolution a t y - infiniteSolution a t x‖ ≤ moment 2 a * |y - x| :=
  solution_space_norm_sub_le a ha t y x

theorem solution_time_lipschitz (a : ℤ → E 2) (ha : Regular a) (x s t : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s x‖ ≤ 2 * moment 2 a * |t - s| :=
  solution_time_norm_sub_le a ha t s x

theorem solution_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t s x y : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s y‖ ≤
      2 * moment 2 a * |t - s| + moment 2 a * |x - y| := by
  calc
    _ ≤ ‖infiniteSolution a t x - infiniteSolution a s x‖ +
        ‖infiniteSolution a s x - infiniteSolution a s y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (solution_time_norm_sub_le a ha t s x)
      (solution_space_norm_sub_le a ha s x y)

end NDEAEvolve.Exp011


-- SOURCE lean/Reconstruction.lean SHA256 296ab241366fd4128bf7d933ed0fb251a53792f0ebbb7c6805e3f5ab78d4f043

/-! Explicit piecewise constant reconstruction of the actual full-grid Cayley
iteration. Space and time indices are clamped to existing nodes/steps. The
right spatial endpoint uses the last grid node, within one cell of the endpoint.
No convergence or reconstruction estimate is assumed in these definitions. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

def nodeValue (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) : E 2 :=
  WithLp.toLp 2 (fun b => v (j,b))

theorem nodeValue_sub (n : ℕ) (v w : Vec (Grid n)) (j : Fin (n+1)) :
    nodeValue n (v-w) j = nodeValue n v j-nodeValue n w j := by
  ext b
  rfl

theorem nodeValue_sampleSolution (n : ℕ) (h : ℝ) (u : ℝ → ℝ → E 2)
    (t : ℝ) (j : Fin (n+1)) :
    nodeValue n (sampleSolution n h u t) j = u t ((j.val:ℝ)*h) := by
  ext b
  rfl

theorem nodeValue_norm_le (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) :
    ‖nodeValue n v j‖ ≤ ‖v‖ := by
  have hs : ‖nodeValue n v j‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [nodeValue, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    have hnonneg (i : Fin (n+1)) : 0≤∑ b : Fin 2, ‖v (i,b)‖^2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg ‖v (i,b)‖
    exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j)
  nlinarith [norm_nonneg (nodeValue n v j), norm_nonneg v]

def spaceIndex (n : ℕ) (h x : ℝ) : Fin (n+1) :=
  ⟨min ⌊x/h⌋₊ n, lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self n)⟩

theorem spaceIndex_distance (n : ℕ) (h x : ℝ) (hh : 0<h)
    (hx : 0≤x) (hL : x≤((n+1:ℕ):ℝ)*h) :
    0≤x-(spaceIndex n h x).val*h ∧ x-(spaceIndex n h x).val*h≤h := by
  have hfloor := Nat.floor_le (div_nonneg hx hh.le)
  have hleft : ((min ⌊x/h⌋₊ n : ℕ):ℝ)≤x/h :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans hfloor
  have hleft' := (le_div_iff₀ hh).mp hleft
  constructor
  · change 0≤x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h
    linarith
  · change x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h≤h
    by_cases hf : ⌊x/h⌋₊≤n
    · rw [min_eq_left hf]
      have hr := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x/h))
      nlinarith
    · rw [min_eq_right (le_of_not_ge hf)]
      push_cast at hL
      nlinarith

def timeIndex (N : ℕ) (k t : ℝ) : ℕ := min ⌊t/k⌋₊ N

theorem timeIndex_le (N : ℕ) (k t : ℝ) : timeIndex N k t≤N :=
  min_le_right _ _

theorem timeIndex_distance (N : ℕ) (k t : ℝ) (hk : 0<k)
    (ht : 0≤t) (hT : t≤(N:ℝ)*k) :
    0≤t-(timeIndex N k t:ℝ)*k ∧ t-(timeIndex N k t:ℝ)*k≤k := by
  have hT' : t≤((N+1:ℕ):ℝ)*k := by
    push_cast
    nlinarith
  exact spaceIndex_distance N k t hk ht hT'

def gridState (n : ℕ) (h k : ℝ) (a : ℤ → E 2) (j : ℕ) : Vec (Grid n) :=
  (symmetric n h k Exp007.Z Exp007.X ^ j)
    (sampleSolution n h (infiniteSolution a) 0)

def reconstruction (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  nodeValue n (gridState n h k a (timeIndex N k t)) (spaceIndex n h x)

theorem gridState_node_error (n : ℕ) (h k : ℝ) (a : ℤ → E 2) (j : ℕ)
    (i : Fin (n+1)) (hh : 0<h) :
    ‖nodeValue n (gridState n h k a j) i-
        infiniteSolution a ((j:ℝ)*k) ((i.val:ℝ)*h)‖ ≤
      classicalGridError n h k j a (sampleSolution n h (infiniteSolution a) 0) /
        Real.sqrt h := by
  have hn := nodeValue_norm_le n (gridState n h k a j-
    sampleSolution n h (infiniteSolution a) ((j:ℝ)*k)) i
  rw [nodeValue_sub, nodeValue_sampleSolution] at hn
  apply (le_div_iff₀ (Real.sqrt_pos.2 hh)).mpr
  simpa only [classicalGridError, gridState, mul_comm] using
    mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg h)

theorem reconstruction_error_bound (n : ℕ) (h k : ℝ) (N : ℕ)
    (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) (hh : 0<h) (hk : 0<k)
    (hx : 0≤x) (hL : x≤((n+1:ℕ):ℝ)*h) (ht : 0≤t) (hT : t≤(N:ℝ)*k) :
    ‖reconstruction n h k N a t x-infiniteSolution a t x‖ ≤
      classicalGridError n h k (timeIndex N k t) a
        (sampleSolution n h (infiniteSolution a) 0) / Real.sqrt h +
          moment 2 a*h+2*moment 2 a*k := by
  let j := timeIndex N k t
  let i := spaceIndex n h x
  let s := (j:ℝ)*k
  let y := (i.val:ℝ)*h
  have hdx : |y-x|≤h := by
    have hd := spaceIndex_distance n h x hh hx hL
    rw [abs_sub_comm, abs_of_nonneg hd.1]
    exact hd.2
  have hdt : |s-t|≤k := by
    have hd := timeIndex_distance N k t hk ht hT
    rw [abs_sub_comm, abs_of_nonneg hd.1]
    exact hd.2
  have hs := (solution_space_lipschitz a ha s x y).trans
    (mul_le_mul_of_nonneg_left hdx (moment_nonneg 2 a))
  have ht' := (solution_time_lipschitz a ha x t s).trans
    (mul_le_mul_of_nonneg_left hdt
      (mul_nonneg (by norm_num : (0:ℝ)≤2) (moment_nonneg 2 a)))
  have hn := gridState_node_error n h k a j i hh
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (reconstruction n h k N a t x) (infiniteSolution a s y) (infiniteSolution a t x)
  have hmiddle := norm_sub_le_norm_sub_add_norm_sub
    (infiniteSolution a s y) (infiniteSolution a s x) (infiniteSolution a t x)
  change ‖reconstruction n h k N a t x-infiniteSolution a s y‖≤_ at hn
  have htotal := htriangle.trans (add_le_add hn (hmiddle.trans (add_le_add hs ht')))
  simpa only [add_assoc] using htotal

end NDEAEvolve.Exp011


-- SOURCE lean/ScheduleBounds.lean SHA256 c3382951dc6b0668d141a38bf726cca3a6a1683077c2478045634c84a3e888db

/-! A bound uniform over every time step of the existing refinement schedule.
The weighted error is converted to a nodal norm estimate that still tends to
zero, despite the factor inverse square root of the mesh spacing. -/
noncomputable section
open Filter
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
open NDEAEvolve.Exp010 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp011

def scheduleCoefficient (q : ℕ) : ℝ :=
  (1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128+2

def nodalBound (q : ℕ) (a : ℤ → E 2) : ℝ :=
  moment 2 a * scheduleCoefficient q * Real.sqrt (8*(cutoff q:ℝ)⁻¹)

theorem scheduleCoefficient_nonneg (q : ℕ) : 0 ≤ scheduleCoefficient q := by
  unfold scheduleCoefficient
  positivity

theorem nodalBound_nonneg (q : ℕ) (a : ℤ → E 2) : 0 ≤ nodalBound q a :=
  mul_nonneg (mul_nonneg (moment_nonneg 2 a) (scheduleCoefficient_nonneg q))
    (Real.sqrt_nonneg _)

theorem scheduled_moment_tail_bound (q : ℕ) (a : ℤ → E 2) :
    moment 2 a / ((cutoff q:ℝ)+1)^2 ≤ moment 2 a*((cutoff q:ℝ)⁻¹)^2 := by
  have hm := cutoff_real_ge_one q
  have hp : 0 < (cutoff q:ℝ)^2 := by positivity
  have hd : (cutoff q:ℝ)^2 ≤ ((cutoff q:ℝ)+1)^2 := by nlinarith
  simpa only [div_eq_mul_inv, inv_pow] using
    div_le_div_of_nonneg_left (moment_nonneg 2 a) hp hd

theorem scheduled_sqrt_ratio (q : ℕ) :
    Real.sqrt (2*Real.pi)*((cutoff q:ℝ)⁻¹)^2 / Real.sqrt (mesh q) =
      Real.sqrt (8*(cutoff q:ℝ)⁻¹) := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  have hr : 0 ≤ (cutoff q:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),
    Real.sq_sqrt (mesh_pos q).le, Real.sq_sqrt (by positivity : 0 ≤ 8*(cutoff q:ℝ)⁻¹),
    mesh_eq_inverse]
  field_simp [Real.pi_ne_zero, hm]
  <;> ring

theorem all_steps_weighted_error_bound (q j : ℕ) (hj : j ≤ stepCount q)
    (a : ℤ → E 2) (ha : Regular a) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) j a
      (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) ≤
        Real.sqrt (2*Real.pi)*moment 2 a*scheduleCoefficient q*((cutoff q:ℝ)⁻¹)^2 := by
  have ht : (j:ℝ)*timeStep q ≤ 1 := by
    calc
      _ ≤ (stepCount q:ℝ)*timeStep q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (timeStep_nonneg q)
      _ = _ := stepCount_timeStep q
  have hb := (classical_grid_error_bound (cutoff q) (gridIndex q)
    (mesh q) (timeStep q) 1 j a
    (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) ha
    (cutoff_pos q) (cutoff_unaliased q) (mesh_period q) (mesh_pos q)
    (cutoff_mesh_le_one q) (timeStep_nonneg q) (timeStep_restriction q) ht).2
  simp only [classicalInitialError, sub_self, norm_zero, mul_zero, zero_add, one_mul] at hb
  have hc : 0 ≤ Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2 :=
    add_nonneg (mul_nonneg (Ct_nonneg _) (sq_nonneg _))
      (mul_nonneg (Cs_nonneg _) (sq_nonneg _))
  have hmass := mul_le_mul_of_nonneg_left (mass_le_moment 2 a ha) hc
  have htail := mul_le_mul_of_nonneg_left (scheduled_moment_tail_bound q a)
    (by norm_num : (0:ℝ) ≤ 2)
  apply hb.trans
  calc
    _ ≤ Real.sqrt (2*Real.pi)*
        ((Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)*moment 2 a +
          2*(moment 2 a*((cutoff q:ℝ)⁻¹)^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hmass htail) (Real.sqrt_nonneg _)
    _ = _ := by rw [cutoff_error_eq_inverse]; unfold scheduleCoefficient; ring

theorem all_steps_nodal_bound (q j : ℕ) (hj : j ≤ stepCount q)
    (a : ℤ → E 2) (ha : Regular a) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) j a
      (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) /
        Real.sqrt (mesh q) ≤ nodalBound q a := by
  apply (div_le_div_of_nonneg_right (all_steps_weighted_error_bound q j hj a ha)
    (Real.sqrt_nonneg _)).trans
  have he : Real.sqrt (2*Real.pi)*moment 2 a*scheduleCoefficient q*((cutoff q:ℝ)⁻¹)^2 /
      Real.sqrt (mesh q) = moment 2 a*scheduleCoefficient q*
        (Real.sqrt (2*Real.pi)*((cutoff q:ℝ)⁻¹)^2 / Real.sqrt (mesh q)) := by ring
  rw [he, scheduled_sqrt_ratio]
  exact le_refl _

theorem scheduleCoefficient_tendsto :
    Tendsto scheduleCoefficient atTop (nhds ((1000/36:ℝ)+Real.pi^2/128+2)) := by
  have h := ((((cutoff_inverse_tendsto_zero.pow 2).const_mul 2).const_add 1).pow 3).const_mul
    (1000/36:ℝ)
  change Tendsto (fun q => (1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128+2)
    atTop (nhds ((1000/36:ℝ)+Real.pi^2/128+2))
  simpa using (h.add_const (Real.pi^2/128)).add_const 2

theorem nodalBound_tendsto_zero (a : ℤ → E 2) :
    Tendsto (fun q => nodalBound q a) atTop (nhds 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (cutoff_inverse_tendsto_zero.const_mul 8)
  simpa [nodalBound] using (scheduleCoefficient_tendsto.const_mul (moment 2 a)).mul hs

end NDEAEvolve.Exp011


-- SOURCE lean/UniformConvergence.lean SHA256 d2e5c12d7b3cff455cbe7c2dabfa792ebc496521ac0f940cced9067002b242d3

/-! Uniform convergence of the actual reconstructed fields over one closed
space-time rectangle, to the classical periodic spinor solution. -/
noncomputable section
open Filter
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

def spaceTimeDomain : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi)

def scheduledReconstruction (q : ℕ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  reconstruction (gridIndex q) (mesh q) (timeStep q) (stepCount q) a t x

def uniformBound (q : ℕ) (a : ℤ → E 2) : ℝ :=
  nodalBound q a + moment 2 a*mesh q + 2*moment 2 a*timeStep q

theorem uniformBound_nonneg (q : ℕ) (a : ℤ → E 2) : 0 ≤ uniformBound q a :=
  add_nonneg (add_nonneg (nodalBound_nonneg q a)
    (mul_nonneg (moment_nonneg 2 a) (mesh_pos q).le))
    (mul_nonneg (mul_nonneg (by norm_num) (moment_nonneg 2 a)) (timeStep_nonneg q))

theorem uniformBound_tendsto_zero (a : ℤ → E 2) :
    Tendsto (fun q => uniformBound q a) atTop (nhds 0) := by
  simpa [uniformBound] using ((nodalBound_tendsto_zero a).add
    (mesh_tendsto_zero.const_mul (moment 2 a))).add
      (timeStep_tendsto_zero.const_mul (2*moment 2 a))

theorem scheduled_reconstruction_error_bound (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    ‖scheduledReconstruction q a t x-infiniteSolution a t x‖ ≤ uniformBound q a := by
  have hL : x ≤ ((gridIndex q+1:ℕ):ℝ)*mesh q := by rw [mesh_period]; exact hx.2
  have hT : t ≤ (stepCount q:ℝ)*timeStep q := by rw [stepCount_timeStep]; exact ht.2
  have hb := reconstruction_error_bound (gridIndex q) (mesh q) (timeStep q) (stepCount q)
    a ha t x (mesh_pos q) (timeStep_pos q) hx.1 hL ht.1 hT
  have hn := all_steps_nodal_bound q (timeIndex (stepCount q) (timeStep q) t)
    (timeIndex_le _ _ _) a ha
  exact hb.trans (add_le_add (add_le_add hn (le_refl _)) (le_refl _))

theorem reconstruction_tendstoUniformlyOn (a : ℤ → E 2) (ha : Regular a) :
    TendstoUniformlyOn (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution a p.1 p.2) atTop spaceTimeDomain := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hb : ∀ᶠ q in atTop, uniformBound q a < ε :=
    (uniformBound_tendsto_zero a).eventually (gt_mem_nhds hε)
  filter_upwards [hb] with q hq
  intro p hp
  have he := scheduled_reconstruction_error_bound q a ha p.1 p.2 hp.1 hp.2
  rw [dist_eq_norm, norm_sub_rev]
  exact he.trans_lt hq

theorem classical_uniform_reconstruction (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    TendstoUniformlyOn (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution a p.1 p.2) atTop spaceTimeDomain :=
  ⟨infiniteSolution_classical a ha, reconstruction_tendstoUniformlyOn a ha⟩

theorem reconstruction_at_point_tendsto (a : ℤ → E 2) (ha : Regular a)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    Tendsto (fun q => scheduledReconstruction q a t x) atTop
      (nhds (infiniteSolution a t x)) :=
  (reconstruction_tendstoUniformlyOn a ha).tendsto_at (x := (t,x)) ⟨ht,hx⟩

end NDEAEvolve.Exp011


-- SOURCE lean/Controls.lean SHA256 e4442c347374e51125c474cc39e8a620b6e90a1d50ccd6bacec55b1e4ce0ad67

/-! Exact index, initialization, inverse-norm, and infinite-support controls
for the explicit reconstructed fields. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011.Controls

theorem spaceIndex_at_zero (n : ℕ) (h : ℝ) : (spaceIndex n h 0).val=0 := by
  simp [spaceIndex]

theorem spaceIndex_at_right_endpoint (n : ℕ) (h : ℝ) (hh : 0<h) :
    (spaceIndex n h (((n+1:ℕ):ℝ)*h)).val=n := by
  change min ⌊(((n+1:ℕ):ℝ)*h)/h⌋₊ n=n
  rw [mul_div_cancel_right₀ _ hh.ne', Nat.floor_natCast,
    min_eq_right (Nat.le_succ n)]

theorem timeIndex_at_zero (N : ℕ) (k : ℝ) : timeIndex N k 0=0 := by
  simp [timeIndex]

theorem timeIndex_at_final_time (N : ℕ) (k : ℝ) (hk : 0<k) :
    timeIndex N k ((N:ℝ)*k)=N := by
  simp [timeIndex, mul_div_cancel_right₀ _ hk.ne']

theorem gridState_initial (n : ℕ) (h k : ℝ) (a : ℤ → E 2) :
    gridState n h k a 0=sampleSolution n h (infiniteSolution a) 0 := by
  simp [gridState]

theorem reconstruction_at_final_time (n : ℕ) (h k : ℝ) (N : ℕ)
    (a : ℤ → E 2) (x : ℝ) (hk : 0<k) :
    reconstruction n h k N a ((N:ℝ)*k) x =
      nodeValue n (gridState n h k a N) (spaceIndex n h x) := by
  rw [reconstruction, timeIndex_at_final_time N k hk]

def nodeSpike (n : ℕ) (j : Fin (n+1)) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => if p.1=j then v p.2 else 0)

theorem nodeValue_spike (n : ℕ) (j : Fin (n+1)) (v : E 2) :
    nodeValue n (nodeSpike n j v) j=v := by
  ext b
  simp [nodeValue, nodeSpike]

theorem nodeSpike_norm (n : ℕ) (j : Fin (n+1)) (v : E 2) :
    ‖nodeSpike n j v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [nodeSpike, Fintype.sum_prod_type, apply_ite]

/-- A single-node error defeats a purported pointwise bound by the weighted
grid norm without the necessary inverse square-root mesh factor. -/
theorem weighted_grid_norm_alone_does_not_bound_node (n : ℕ) (h : ℝ)
    (hh : 0<h) (hsmall : h<1) (j : Fin (n+1)) :
    Real.sqrt h*‖nodeSpike n j Exp007.Controls.initialSpinor‖ <
      ‖nodeValue n (nodeSpike n j Exp007.Controls.initialSpinor) j‖ := by
  rw [nodeValue_spike, nodeSpike_norm, Exp007.Controls.initialSpinor_norm, mul_one]
  nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]

def regularCoefficients (m : ℤ) : E 2 :=
  ((1/2 : ℂ)^Encodable.encode m / (frequencyWeight 2 m : ℂ)) •
    Exp007.Controls.initialSpinor

theorem regular_coefficient_norm (m : ℤ) :
    ‖regularCoefficients m‖=(1/2 : ℝ)^Encodable.encode m/frequencyWeight 2 m := by
  simp [regularCoefficients, norm_smul, norm_pow, Exp007.Controls.initialSpinor_norm,
    Real.norm_eq_abs, abs_of_nonneg (frequencyWeight_nonneg 2 m)]

theorem regular_weighted_norm (m : ℤ) :
    frequencyWeight 2 m*‖regularCoefficients m‖=(1/2 : ℝ)^Encodable.encode m := by
  rw [regular_coefficient_norm]
  exact mul_div_cancel₀ _ (frequencyWeight_two_pos m).ne'

theorem coefficients_regular : Regular regularCoefficients := by
  change Summable (fun m : ℤ => frequencyWeight 2 m*‖regularCoefficients m‖)
  simp only [regular_weighted_norm]
  exact summable_geometric_two_encode

theorem regular_coefficient_nonzero (m : ℤ) : regularCoefficients m≠0 := by
  apply norm_ne_zero_iff.mp
  rw [regular_coefficient_norm]
  have hw := frequencyWeight_two_pos m
  positivity

theorem regular_coefficients_infinite_support : (Function.support regularCoefficients).Infinite := by
  have hs : Function.support regularCoefficients=Set.univ := by
    ext m
    simp [Function.mem_support, regular_coefficient_nonzero]
  rw [hs]
  exact Set.infinite_univ

theorem infinite_support_uniform_classical_example :
    (Function.support regularCoefficients).Infinite ∧
    IsClassicalPeriodicSolution (infiniteSolution regularCoefficients) ∧
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q regularCoefficients p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution regularCoefficients p.1 p.2)
      Filter.atTop spaceTimeDomain :=
  ⟨regular_coefficients_infinite_support,
    classical_uniform_reconstruction regularCoefficients coefficients_regular⟩

end NDEAEvolve.Exp011.Controls




-- SOURCE lean/EnergyLocal.lean SHA256 89b76b31ce9c2f273146ef2e55d6cbe32a181568bb69de2dc11ed7b5c09ec67c

/-! Local conservation for arbitrary classical periodic solutions. No Fourier
representation is assumed for the solution in these statements. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp010
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp012

def energyDensity (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ := ‖u t x‖ ^ 2

def densityDerivative (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (deriv (fun s => u s x) t)).re

def flux (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (u t) x)).re

theorem potential_selfadjoint :
    IsSelfAdjoint (operatorOf (Exp007.Z + Exp007.X)) := by
  change star (operatorOf (Exp007.Z + Exp007.X)) = _
  simpa only [operatorOf, map_star] using
    congrArg (fun M : Mat 2 => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M)
      (hermitian_star (Exp007.Z_isHermitian.add Exp007.X_isHermitian))

theorem potential_cancellation (w : E 2) :
    (inner ℂ w ((-Complex.I) • operatorOf (Exp007.Z + Exp007.X) w)).re = 0 := by
  have h := potential_selfadjoint.isSymmetric.im_inner_self_apply w
  change (inner ℂ w (operatorOf (Exp007.Z + Exp007.X) w)).im = 0 at h
  rw [inner_smul_right]
  simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, sub_neg_eq_add, zero_add, zero_sub, neg_neg] using h

theorem imaginary_self_cancellation (w : E 2) :
    (inner ℂ w (Complex.I • w)).re = 0 := by
  have h := inner_self_im (𝕜 := ℂ) w
  change (inner ℂ w w).im = 0 at h
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, h, sub_self]

theorem periodic_deriv {f : ℝ → E 2} {L : ℝ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have hd := (hf (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
  have he : (fun y => f (y + L)) = f := funext hp
  simpa only [Function.comp_def, id_eq, one_smul, he] using hd.deriv.symm

theorem density_time_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    HasDerivAt (fun s => energyDensity u s x) (densityDerivative u t x) t := by
  letI : InnerProductSpace ℝ (E 2) := InnerProductSpace.rclikeToReal ℂ (E 2)
  simpa only [energyDensity, densityDerivative, real_inner_eq_re_inner ℂ] using!
    (hu.time_differentiable t x).hasDerivAt.norm_sq

theorem energyDensity_continuous (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) :
    Continuous (fun p : ℝ × ℝ => energyDensity u p.1 p.2) :=
  hu.continuous_solution.norm.pow 2

theorem densityDerivative_continuous (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) :
    Continuous (fun p : ℝ × ℝ => densityDerivative u p.1 p.2) := by
  exact (Complex.continuous_re.comp
    (hu.continuous_solution.inner hu.continuous_time_derivative)).const_mul 2

theorem classical_time_derivative (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    deriv (fun s => u s x) t = Complex.I • deriv (deriv (u t)) x +
      (-Complex.I) • operatorOf (Exp007.Z + Exp007.X) (u t x) := by
  have h := congrArg (fun z : E 2 => (-Complex.I) • z) (hu.schrodinger t x)
  simpa [smul_add, smul_smul, smul_neg, neg_smul] using h

theorem densityDerivative_eq_spatial_expression (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    densityDerivative u t x =
      2 * (inner ℂ (u t x) (Complex.I • deriv (deriv (u t)) x)).re := by
  unfold densityDerivative
  rw [classical_time_derivative u hu t x]
  simp only [inner_add_right, Complex.add_re, potential_cancellation, add_zero]

/-- The spatial derivative of the periodic flux is the actual time derivative
of the squared solution norm. -/
theorem flux_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    HasDerivAt (flux u t) (densityDerivative u t x) x := by
  rw [densityDerivative_eq_spatial_expression u hu t x]
  have hd := (hu.space_differentiable t x).hasDerivAt.inner ℂ
    ((hu.second_space_differentiable t x).hasDerivAt.const_smul Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [flux, Complex.add_re, imaginary_self_cancellation] using! hr.const_mul 2

theorem flux_periodic (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t : ℝ) :
    Function.Periodic (flux u t) (2 * Real.pi) := by
  have hp := periodic_deriv (hu.space_differentiable t) (hu.periodic t)
  intro x
  simp only [flux, hu.periodic t x, hp x]

theorem classical_sub_time_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (fun s => u s x - v s x) t =
      deriv (fun s => u s x) t - deriv (fun s => v s x) t :=
  deriv_sub (hu.time_differentiable t x) (hv.time_differentiable t x)

theorem classical_sub_space_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (fun y => u t y - v t y) x = deriv (u t) x - deriv (v t) x :=
  deriv_sub (hu.space_differentiable t x) (hv.space_differentiable t x)

theorem classical_sub_second_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (deriv (fun y => u t y - v t y)) x =
      deriv (deriv (u t)) x - deriv (deriv (v t)) x := by
  have he : deriv (fun y => u t y - v t y) =
      fun y => deriv (u t) y - deriv (v t) y :=
    funext (classical_sub_space_derivative u v hu hv t)
  rw [he]
  exact deriv_sub (hu.second_space_differentiable t x) (hv.second_space_differentiable t x)

theorem classical_sub (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) :
    IsClassicalPeriodicSolution (fun t x => u t x - v t x) where
  time_differentiable t x := (hu.time_differentiable t x).sub (hv.time_differentiable t x)
  space_differentiable t x := (hu.space_differentiable t x).sub (hv.space_differentiable t x)
  second_space_differentiable t x := by
    have he : deriv (fun y => u t y - v t y) =
        fun y => deriv (u t) y - deriv (v t) y :=
      funext (classical_sub_space_derivative u v hu hv t)
    rw [he]
    exact (hu.second_space_differentiable t x).sub (hv.second_space_differentiable t x)
  continuous_solution := hu.continuous_solution.sub hv.continuous_solution
  continuous_time_derivative := by
    simpa only [classical_sub_time_derivative u v hu hv] using
      hu.continuous_time_derivative.sub hv.continuous_time_derivative
  continuous_space_derivative := by
    simpa only [classical_sub_space_derivative u v hu hv] using
      hu.continuous_space_derivative.sub hv.continuous_space_derivative
  continuous_second_derivative := by
    simpa only [classical_sub_second_derivative u v hu hv] using
      hu.continuous_second_derivative.sub hv.continuous_second_derivative
  periodic t x := by simp only [hu.periodic t x, hv.periodic t x]
  schrodinger t x := by
    rw [classical_sub_time_derivative u v hu hv, classical_sub_second_derivative u v hu hv,
      smul_sub, hu.schrodinger t x, hv.schrodinger t x, map_sub]
    abel

theorem classical_zero : IsClassicalPeriodicSolution (fun _ _ : ℝ => (0 : E 2)) := by
  have ha : Regular (fun _ : ℤ => (0 : E 2)) := by simp [Regular]
  have he : Exp009.infiniteSolution (fun _ : ℤ => (0 : E 2)) =
      (fun _ _ : ℝ => (0 : E 2)) := by
    funext t x
    simp [Exp009.infiniteSolution, Exp008.modeSolution, Exp008.modeOrbit]
  simpa only [he] using infiniteSolution_classical (fun _ : ℤ => (0 : E 2)) ha

end NDEAEvolve.Exp012


-- SOURCE lean/EnergyConservation.lean SHA256 58c15c9ad6624b4f94915f3e755af775bc0c7ab53b6ff729703fa5044d420818

/-! Energy conservation for every classical periodic solution, on a period
interval with arbitrary real base point. A local compact rectangle supplies
the domination required to differentiate the integral; there is no additional
global bound or Fourier representation assumption. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp012

theorem compact_derivative_bound (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b t : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Ioo (t-1) (t+1), ∀ x ∈ uIcc a b, ‖g s x‖≤C := by
  have hcompact : IsCompact (Icc (t-1) (t+1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C,?_⟩
  intro s hs x hx
  exact hC (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩

theorem joint_interval_hasDerivAt (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hd : ∀ s x, HasDerivAt (fun t => f t x) (g s x) s) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f s x) (∫ x in a..b, g t x) t := by
  obtain ⟨C,hC⟩ := compact_derivative_bound g hg a b t
  have hf_slice (s : ℝ) : Continuous (f s) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hg_slice (s : ℝ) : Continuous (g s) :=
    hg.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := g) (a := a) (b := b)
    (s := Ioo (t-1) (t+1)) (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall fun s => (hf_slice s).aestronglyMeasurable
  · exact (hf_slice t).intervalIntegrable a b
  · exact (hg_slice t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x hx s hs => hC s hs x (uIoc_subset_uIcc hx)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ s _ => hd s x

def energy (u : ℝ → ℝ → E 2) (b t : ℝ) : ℝ :=
  ∫ x in b..b+2*Real.pi, ‖u t x‖^2

theorem energy_intervalIntegrable (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    IntervalIntegrable (fun x => ‖u t x‖^2) volume b (b+2*Real.pi) := by
  have hc : Continuous (energyDensity u t) :=
    (energyDensity_continuous u hu).comp (f := fun x : ℝ => (t,x))
      (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable b (b+2*Real.pi)

theorem densityDerivative_intervalIntegrable (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    IntervalIntegrable (densityDerivative u t) volume b (b+2*Real.pi) := by
  have hc : Continuous (densityDerivative u t) :=
    (densityDerivative_continuous u hu).comp (f := fun x : ℝ => (t,x))
      (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable b (b+2*Real.pi)

theorem energy_time_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    HasDerivAt (energy u b) (∫ x in b..b+2*Real.pi, densityDerivative u t x) t :=
  joint_interval_hasDerivAt (energyDensity u) (densityDerivative u)
    (energyDensity_continuous u hu) (densityDerivative_continuous u hu)
    (density_time_hasDerivAt u hu) b (b+2*Real.pi) t

theorem densityDerivative_integral_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    (∫ x in b..b+2*Real.pi, densityDerivative u t x)=0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux u t) (f' := densityDerivative u t) (a := b) (b := b+2*Real.pi)
    (fun x _ => flux_hasDerivAt u hu t x) (densityDerivative_intervalIntegrable u hu b t)
  rw [flux_periodic u hu t b, sub_self] at h
  exact h

theorem energy_hasDerivAt_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    HasDerivAt (energy u b) 0 t := by
  have h := energy_time_hasDerivAt u hu b t
  rw [densityDerivative_integral_zero u hu b t] at h
  exact h

theorem energy_eq (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (b s t : ℝ) : energy u b s=energy u b t :=
  is_const_of_deriv_eq_zero
    (f := energy u b)
    (fun r => (energy_hasDerivAt_zero u hu b r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero u hu b r).deriv) s t

theorem energy_eq_initial (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    energy u b t=energy u b 0 :=
  energy_eq u hu b t 0

end NDEAEvolve.Exp012


-- SOURCE lean/EnergySeparation.lean SHA256 59ff4ab80dd2bd54615dc04d8014b5854e266e4e3832e66421a7b262f6bb5601

/-! Continuous spinor fields are separated by their nonnegative integral
energy. Allowing an arbitrary interval base covers every real spatial point
directly, including the left endpoint. -/
noncomputable section
open NDEAEvolve.Exp003
open MeasureTheory
namespace NDEAEvolve.Exp012

theorem norm_sq_integral_pos_of_ne_zero (f : ℝ → E 2) (hf : Continuous f)
    (b L : ℝ) (hL : 0 < L) (hb : f b ≠ 0) :
    0 < ∫ x in b..b+L, ‖f x‖^2 := by
  apply intervalIntegral.integral_pos (by linarith : b < b+L)
    (hf.norm.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · refine ⟨b, ⟨le_refl _, by linarith⟩, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem norm_sq_integrals_separate_zero (f : ℝ → E 2) (hf : Continuous f)
    (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖f x‖^2)=0) : f=0 := by
  funext x
  by_contra hx
  have hp := norm_sq_integral_pos_of_ne_zero f hf x L hL hx
  rw [hz x] at hp
  exact (lt_irrefl 0 hp)

theorem norm_sq_integrals_separate (f g : ℝ → E 2)
    (hf : Continuous f) (hg : Continuous g) (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖f x-g x‖^2)=0) : f=g := by
  have h := norm_sq_integrals_separate_zero (fun x => f x-g x) (hf.sub hg) L hL hz
  funext x
  exact sub_eq_zero.mp (congrFun h x)

end NDEAEvolve.Exp012


-- SOURCE lean/ClassicalUniqueness.lean SHA256 1a90a2931740bb71e7813d71844f5be983a581bfb8549dbe12bbe9bd3e0e2744

/-! Uniqueness for arbitrary classical periodic functions, and identification
of the previously reconstructed numerical limit with that unique solution. -/
noncomputable section
open MeasureTheory Filter
open NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010 NDEAEvolve.Exp011
namespace NDEAEvolve.Exp012

theorem classical_difference_energy_conserved (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (b s t : ℝ) :
    (∫ x in b..b+2*Real.pi, ‖u s x-v s x‖^2) =
      ∫ x in b..b+2*Real.pi, ‖u t x-v t x‖^2 :=
  energy_eq (fun r x => u r x-v r x) (classical_sub u v hu hv) b s t

theorem classical_unique_at_time (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (s : ℝ) (hs : ∀ x, u s x=v s x) : u=v := by
  funext t
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  apply norm_sq_integrals_separate (u t) (v t)
    (hu.continuous_solution.comp hp) (hv.continuous_solution.comp hp)
    (2*Real.pi) (by positivity)
  intro b
  have h := classical_difference_energy_conserved u v hu hv b t s
  simpa [hs] using h

theorem classical_unique (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (h0 : ∀ x, u 0 x=v 0 x) : u=v :=
  classical_unique_at_time u v hu hv 0 h0

theorem classical_zero_of_initial_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (h0 : ∀ x, u 0 x=0) : u=0 :=
  classical_unique u 0 hu classical_zero h0

theorem classical_eq_infiniteSolution (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x) : u=infiniteSolution a :=
  classical_unique u (infiniteSolution a) hu (infiniteSolution_classical a ha) h0

theorem classical_existsUnique (a : ℤ → E 2) (ha : Regular a) :
    ∃! u : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧
      ∀ x, u 0 x=infiniteSolution a 0 x := by
  refine ⟨infiniteSolution a, ⟨infiniteSolution_classical a ha, fun _ => rfl⟩, ?_⟩
  intro u hu
  exact classical_eq_infiniteSolution a ha u hu.1 hu.2

theorem reconstruction_converges_to_classical (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x) :
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => u p.1 p.2) atTop spaceTimeDomain := by
  rw [classical_eq_infiniteSolution a ha u hu h0]
  exact reconstruction_tendstoUniformlyOn a ha

theorem reconstruction_error_to_classical (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    ‖scheduledReconstruction q a t x-u t x‖ ≤ uniformBound q a := by
  rw [classical_eq_infiniteSolution a ha u hu h0]
  exact scheduled_reconstruction_error_bound q a ha t x ht hx

end NDEAEvolve.Exp012


-- SOURCE lean/Controls.lean SHA256 14e602688dcda03fd1ff0db427f99e8f10c8600c2d489cdc36c3c40b56491ecc

/-! Exact controls for classical uniqueness. A nonzero frequency-one solution
and the zero solution distinguish the initial-data hypothesis from merely
sharing a PDE. Terminal matching also tests recovery at an earlier time. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp012.Controls

def oneModeCoefficients (m : ℤ) : E 2 :=
  if m = 1 then Exp007.Controls.initialSpinor else 0

def oneModeSolution : ℝ → ℝ → E 2 := infiniteSolution oneModeCoefficients

theorem one_mode_regular : Regular oneModeCoefficients := by
  have he : (fun m : ℤ => frequencyWeight 2 m * ‖oneModeCoefficients m‖) =
      (fun m : ℤ => if m = 1 then frequencyWeight 2 1 * ‖Exp007.Controls.initialSpinor‖ else 0) := by
    funext m
    by_cases hm : m = 1 <;> simp [oneModeCoefficients, hm]
  unfold Regular
  rw [he]
  exact (hasSum_ite_eq (1 : ℤ) _).summable

theorem one_mode_support_singleton : Function.support oneModeCoefficients = {1} := by
  have hv : Exp007.Controls.initialSpinor ≠ 0 := norm_ne_zero_iff.mp (by
    rw [Exp007.Controls.initialSpinor_norm]
    norm_num)
  ext m
  by_cases hm : m = 1 <;> simp [Function.mem_support, oneModeCoefficients, hm, hv]

theorem one_mode_solution_eq (t x : ℝ) :
    oneModeSolution t x = modeSolution 1 Exp007.Controls.initialSpinor t x := by
  unfold oneModeSolution infiniteSolution
  rw [tsum_eq_single (1 : ℤ)]
  · simp [oneModeCoefficients]
  · intro m hm
    simp [oneModeCoefficients, hm, modeSolution, modeOrbit]

theorem one_mode_classical : IsClassicalPeriodicSolution oneModeSolution :=
  infiniteSolution_classical oneModeCoefficients one_mode_regular

theorem one_mode_norm_one (t x : ℝ) : ‖oneModeSolution t x‖ = 1 := by
  rw [one_mode_solution_eq, modeSolution_norm, Exp007.Controls.initialSpinor_norm]

/-- Two classical solutions of this same PDE differ when their data differ. -/
theorem initial_data_cannot_be_omitted :
    ∃ u v : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧
      IsClassicalPeriodicSolution v ∧ u 0 0 ≠ v 0 0 ∧ u ≠ v := by
  have hne : oneModeSolution 0 0 ≠ 0 := by
    intro h
    have hn := one_mode_norm_one 0 0
    rw [h, norm_zero] at hn
    norm_num at hn
  refine ⟨oneModeSolution, 0, one_mode_classical, classical_zero, hne, ?_⟩
  intro he
  exact hne (congrFun (congrFun he 0) 0)

theorem one_mode_energy (b t : ℝ) : energy oneModeSolution b t = 2 * Real.pi := by
  unfold energy
  simp_rw [one_mode_norm_one, one_pow]
  simp

theorem zero_data_unique :
    ∃! u : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧ ∀ x, u 0 x = 0 := by
  refine ⟨0, ⟨classical_zero, fun _ => rfl⟩, ?_⟩
  intro u hu
  exact classical_zero_of_initial_zero u hu.1 hu.2

/-- Matching the nonzero solution at time one recovers its earlier initial
profile. The competing classical solution is an arbitrary function. -/
theorem terminal_match_recovers_initial (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (h1 : ∀ x, u 1 x = oneModeSolution 1 x) (x : ℝ) :
    u 0 x = Exp006.phase x • Exp007.Controls.initialSpinor := by
  have he := classical_unique_at_time u oneModeSolution hu one_mode_classical 1 h1
  calc
    _ = oneModeSolution 0 x := congrFun (congrFun he 0) x
    _ = _ := by rw [one_mode_solution_eq]; simp

/-- The chosen convention is `density_t = flux_x`: frequency +1 has flux -2. -/
theorem one_mode_flux_sign : flux oneModeSolution 0 0 = -2 := by
  have hvalue : oneModeSolution 0 0 = Exp007.Controls.initialSpinor := by
    rw [one_mode_solution_eq]
    simp
  have hfun : oneModeSolution 0 = modeSolution 1 Exp007.Controls.initialSpinor 0 :=
    funext (one_mode_solution_eq 0)
  have hd : deriv (oneModeSolution 0) 0 = Complex.I • Exp007.Controls.initialSpinor := by
    rw [hfun, (modeSolution_space_hasDerivAt 1 Exp007.Controls.initialSpinor 0 0).deriv]
    simp
  unfold flux
  rw [hvalue, hd, smul_smul, Complex.I_mul_I, neg_one_smul, inner_neg_right,
    inner_self_eq_norm_sq_to_K, Exp007.Controls.initialSpinor_norm]
  norm_num

end NDEAEvolve.Exp012.Controls




-- SOURCE lean/GenericClassical.lean SHA256 26198a2e7dbc815ef665c663c1c3c991cba5926a67ac1e5361530db1c4ee33ec

/-! Classical periodic Schrödinger systems in a complex Hilbert space. The
potential and forcing may depend on time and position. Actual derivatives
and their joint continuity are required; no existence claim is built in. -/
noncomputable section
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp013

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Classical solution of `i u_t = -u_xx + V(t,x)u + f(t,x)`, periodic with
period `L`. Positivity of the period and symmetry of the potential are separate
hypotheses of the results that use them. -/
structure IsClassicalPeriodicSolution (L : ℝ) (V : ℝ → ℝ → H →L[ℂ] H)
    (f u : ℝ → ℝ → H) : Prop where
  time_differentiable : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space_differentiable : ∀ t x, DifferentiableAt ℝ (u t) x
  second_space_differentiable : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x
  continuous_solution : Continuous (fun p : ℝ × ℝ => u p.1 p.2)
  continuous_time_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1)
  continuous_space_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)
  continuous_second_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (u p.1)) p.2)
  periodic : ∀ t, Function.Periodic (u t) L
  schrodinger : ∀ t x, Complex.I • deriv (fun s => u s x) t =
    -deriv (deriv (u t)) x + V t x (u t x) + f t x

def energyDensity (u : ℝ → ℝ → H) (t x : ℝ) : ℝ := ‖u t x‖ ^ 2

def densityDerivative (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (deriv (fun s => u s x) t)).re

def flux (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (u t) x)).re

def fluxDerivative (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (deriv (u t)) x)).re

def forcingWork (f u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) ((-Complex.I) • f t x)).re

theorem potential_cancellation (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (w : H) :
    (inner ℂ w ((-Complex.I) • A w)).re = 0 := by
  have h := hA.isSymmetric.im_inner_self_apply w
  change (inner ℂ w (A w)).im = 0 at h
  rw [inner_smul_right]
  simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, sub_neg_eq_add, zero_add,
    zero_sub, neg_neg] using h

omit [CompleteSpace H] in
theorem imaginary_self_cancellation (w : H) :
    (inner ℂ w (Complex.I • w)).re = 0 := by
  have h := inner_self_im (𝕜 := ℂ) w
  change (inner ℂ w w).im = 0 at h
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, h, sub_self]

omit [CompleteSpace H] in
theorem periodic_deriv {g : ℝ → H} {L : ℝ}
    (hg : Differentiable ℝ g) (hp : Function.Periodic g L) :
    Function.Periodic (deriv g) L := by
  intro x
  have hd := (hg (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
  have he : (fun y => g (y + L)) = g := funext hp
  simpa only [Function.comp_def, id_eq, one_smul, he] using hd.deriv.symm

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f g : ℝ → ℝ → H}

omit [CompleteSpace H] in
theorem density_time_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    HasDerivAt (fun s => energyDensity u s x) (densityDerivative u t x) t := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  simpa only [energyDensity, densityDerivative, real_inner_eq_re_inner ℂ] using!
    (hu.time_differentiable t x).hasDerivAt.norm_sq

omit [CompleteSpace H] in
theorem energyDensity_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => energyDensity u p.1 p.2) :=
  hu.continuous_solution.norm.pow 2

omit [CompleteSpace H] in
theorem densityDerivative_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => densityDerivative u p.1 p.2) :=
  (Complex.continuous_re.comp
    (hu.continuous_solution.inner hu.continuous_time_derivative)).const_mul 2

omit [CompleteSpace H] in
theorem fluxDerivative_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => fluxDerivative u p.1 p.2) :=
  (Complex.continuous_re.comp
    (hu.continuous_solution.inner
      (hu.continuous_second_derivative.const_smul Complex.I))).const_mul 2

omit [CompleteSpace H] in
theorem classical_time_derivative (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    deriv (fun s => u s x) t = Complex.I • deriv (deriv (u t)) x +
      (-Complex.I) • V t x (u t x) + (-Complex.I) • f t x := by
  have h := congrArg (fun z : H => (-Complex.I) • z) (hu.schrodinger t x)
  simpa [smul_add, smul_smul, smul_neg, neg_smul] using h

/-- Pointwise forced mass balance. No differentiability of the potential or
forcing is used: the potential cancels by pointwise self-adjointness. -/
theorem densityDerivative_eq_fluxDerivative_add_forcingWork (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (t x : ℝ) :
    densityDerivative u t x = fluxDerivative u t x + forcingWork f u t x := by
  unfold densityDerivative fluxDerivative forcingWork
  rw [classical_time_derivative u hu t x]
  simp only [inner_add_right, Complex.add_re, potential_cancellation _ (hV t x), add_zero]
  ring

/-- Although no separate continuity of the forcing is assumed, its work along
a classical solution is continuous by the actual local balance identity. -/
theorem forcingWork_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) :
    Continuous (fun p : ℝ × ℝ => forcingWork f u p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => forcingWork f u p.1 p.2) =
      fun p => densityDerivative u p.1 p.2 - fluxDerivative u p.1 p.2 := by
    funext p
    linarith [densityDerivative_eq_fluxDerivative_add_forcingWork u hu hV p.1 p.2]
  rw [he]
  exact (densityDerivative_continuous u hu).sub (fluxDerivative_continuous u hu)

omit [CompleteSpace H] in
theorem flux_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    HasDerivAt (flux u t) (fluxDerivative u t x) x := by
  have hd := (hu.space_differentiable t x).hasDerivAt.inner ℂ
    ((hu.second_space_differentiable t x).hasDerivAt.const_smul Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [flux, fluxDerivative, Complex.add_re, imaginary_self_cancellation] using! hr.const_mul 2

omit [CompleteSpace H] in
theorem flux_periodic (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t : ℝ) :
    Function.Periodic (flux u t) L := by
  have hp := periodic_deriv (hu.space_differentiable t) (hu.periodic t)
  intro x
  simp only [flux, hu.periodic t x, hp x]

omit [CompleteSpace H] in
theorem classical_sub_time_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (fun s => u s x - v s x) t =
      deriv (fun s => u s x) t - deriv (fun s => v s x) t :=
  deriv_sub (hu.time_differentiable t x) (hv.time_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub_space_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (fun y => u t y - v t y) x = deriv (u t) x - deriv (v t) x :=
  deriv_sub (hu.space_differentiable t x) (hv.space_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub_second_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (deriv (fun y => u t y - v t y)) x =
      deriv (deriv (u t)) x - deriv (deriv (v t)) x := by
  have he : deriv (fun y => u t y - v t y) =
      fun y => deriv (u t) y - deriv (v t) y :=
    funext (classical_sub_space_derivative u v hu hv t)
  rw [he]
  exact deriv_sub (hu.second_space_differentiable t x) (hv.second_space_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) :
    IsClassicalPeriodicSolution L V (fun t x => f t x - g t x)
      (fun t x => u t x - v t x) where
  time_differentiable t x := (hu.time_differentiable t x).sub (hv.time_differentiable t x)
  space_differentiable t x := (hu.space_differentiable t x).sub (hv.space_differentiable t x)
  second_space_differentiable t x := by
    have he : deriv (fun y => u t y - v t y) =
        fun y => deriv (u t) y - deriv (v t) y :=
      funext (classical_sub_space_derivative u v hu hv t)
    rw [he]
    exact (hu.second_space_differentiable t x).sub (hv.second_space_differentiable t x)
  continuous_solution := hu.continuous_solution.sub hv.continuous_solution
  continuous_time_derivative := by
    simpa only [classical_sub_time_derivative u v hu hv] using
      hu.continuous_time_derivative.sub hv.continuous_time_derivative
  continuous_space_derivative := by
    simpa only [classical_sub_space_derivative u v hu hv] using
      hu.continuous_space_derivative.sub hv.continuous_space_derivative
  continuous_second_derivative := by
    simpa only [classical_sub_second_derivative u v hu hv] using
      hu.continuous_second_derivative.sub hv.continuous_second_derivative
  periodic t x := by simp only [hu.periodic t x, hv.periodic t x]
  schrodinger t x := by
    rw [classical_sub_time_derivative u v hu hv, classical_sub_second_derivative u v hu hv,
      smul_sub, hu.schrodinger t x, hv.schrodinger t x, map_sub]
    abel

omit [CompleteSpace H] in
theorem classical_sub_same_forcing (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v) :
    IsClassicalPeriodicSolution L V 0 (fun t x => u t x - v t x) := by
  simpa only [sub_self, Pi.zero_def] using classical_sub u v hu hv

omit [CompleteSpace H] in
theorem classical_zero (L : ℝ) (V : ℝ → ℝ → H →L[ℂ] H) :
    IsClassicalPeriodicSolution L V 0 0 where
  time_differentiable _ _ := differentiableAt_const _
  space_differentiable _ _ := differentiableAt_const _
  second_space_differentiable _ x := by
    simpa only [Pi.zero_def, deriv_const'] using
      (differentiableAt_const (0 : H) : DifferentiableAt ℝ (fun _ : ℝ => (0 : H)) x)
  continuous_solution := continuous_const
  continuous_time_derivative := by
    simpa only [Pi.zero_def, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  continuous_space_derivative := by
    simpa only [Pi.zero_def, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  continuous_second_derivative := by
    simpa only [Pi.zero_def, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  periodic _ _ := rfl
  schrodinger _ _ := by simp [Pi.zero_def, deriv_const]

end NDEAEvolve.Exp013


-- SOURCE lean/GenericEnergy.lean SHA256 f1668d4704a8527839e8ffec5fff535b923c12e28285be7434ac62045d64dece

/-! Energy balance and homogeneous conservation in a complex Hilbert space.
The derivative majorant is obtained on local compact rectangles. The potential
may vary in time and position; only its pointwise self-adjointness is used. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval
namespace NDEAEvolve.Exp013

theorem compact_derivative_bound (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b t : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Ioo (t-1) (t+1), ∀ x ∈ uIcc a b, ‖g s x‖ ≤ C := by
  have hcompact : IsCompact (Icc (t-1) (t+1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C,?_⟩
  intro s hs x hx
  exact hC (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩

theorem joint_interval_hasDerivAt (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hd : ∀ s x, HasDerivAt (fun t => f t x) (g s x) s) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f s x) (∫ x in a..b, g t x) t := by
  obtain ⟨C,hC⟩ := compact_derivative_bound g hg a b t
  have hf_slice (s : ℝ) : Continuous (f s) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hg_slice (s : ℝ) : Continuous (g s) :=
    hg.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := g) (a := a) (b := b)
    (s := Ioo (t-1) (t+1)) (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall fun s => (hf_slice s).aestronglyMeasurable
  · exact (hf_slice t).intervalIntegrable a b
  · exact (hg_slice t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x hx s hs => hC s hs x (uIoc_subset_uIcc hx)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ s _ => hd s x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energy (u : ℝ → ℝ → H) (b L t : ℝ) : ℝ :=
  ∫ x in b..b+L, ‖u t x‖^2

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem energy_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fun x => ‖u t x‖^2) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (energyDensity u t) := (energyDensity_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem densityDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (densityDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (densityDerivative u t) := (densityDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem fluxDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fluxDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fluxDerivative u t) := (fluxDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem forcingWork_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    IntervalIntegrable (forcingWork f u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (forcingWork f u t) := (forcingWork_continuous u hu hV).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem energy_time_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, densityDerivative u t x) t :=
  joint_interval_hasDerivAt (energyDensity u) (densityDerivative u)
    (energyDensity_continuous u hu) (densityDerivative_continuous u hu)
    (density_time_hasDerivAt u hu) b (b+L) t

theorem fluxDerivative_integral_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    (∫ x in b..b+L, fluxDerivative u t x) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux u t) (f' := fluxDerivative u t) (a := b) (b := b+L)
    (fun x _ => flux_hasDerivAt u hu t x) (fluxDerivative_intervalIntegrable u hu b t)
  rw [flux_periodic u hu t b, sub_self] at h
  exact h

theorem densityDerivative_integral_eq_forcingWork (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    (∫ x in b..b+L, densityDerivative u t x) = ∫ x in b..b+L, forcingWork f u t x := by
  calc
    (∫ x in b..b+L, densityDerivative u t x) =
        ∫ x in b..b+L, fluxDerivative u t x + forcingWork f u t x :=
      intervalIntegral.integral_congr
        (fun x _ => densityDerivative_eq_fluxDerivative_add_forcingWork u hu hV t x)
    _ = (∫ x in b..b+L, fluxDerivative u t x) +
        ∫ x in b..b+L, forcingWork f u t x :=
      intervalIntegral.integral_add (fluxDerivative_intervalIntegrable u hu b t)
        (forcingWork_intervalIntegrable u hu hV b t)
    _ = ∫ x in b..b+L, forcingWork f u t x := by
      rw [fluxDerivative_integral_zero u hu b t, zero_add]

theorem energy_time_hasDerivAt_work (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, forcingWork f u t x) t := by
  have h := energy_time_hasDerivAt u hu b t
  rw [densityDerivative_integral_eq_forcingWork u hu hV b t] at h
  exact h

theorem energy_hasDerivAt_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) 0 t := by
  simpa [forcingWork] using energy_time_hasDerivAt_work u hu hV b t

theorem energy_eq (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    energy u b L s = energy u b L t :=
  is_const_of_deriv_eq_zero (f := energy u b L)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).deriv) s t

theorem energy_eq_initial (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    energy u b L t = energy u b L 0 :=
  energy_eq u hu hV b t 0

end NDEAEvolve.Exp013


-- SOURCE lean/GenericUniqueness.lean SHA256 93d1fed2c93b69ff1d9614faaef4a7150e0a392cbe9e206e88b1cfefd451cab9

/-! Uniqueness within the classical periodic solution class for a common
time- and space-dependent self-adjoint potential and common forcing. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp013

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sq_integral_pos_of_ne_zero (w : ℝ → H) (hw : Continuous w)
    (b L : ℝ) (hL : 0 < L) (hb : w b ≠ 0) :
    0 < ∫ x in b..b+L, ‖w x‖^2 := by
  apply intervalIntegral.integral_pos (by linarith : b < b+L)
    (hw.norm.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · refine ⟨b, ⟨le_refl _, by linarith⟩, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem norm_sq_integrals_separate_zero (w : ℝ → H) (hw : Continuous w)
    (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖w x‖^2) = 0) : w = 0 := by
  funext x
  by_contra hx
  have hp := norm_sq_integral_pos_of_ne_zero w hw x L hL hx
  rw [hz x] at hp
  exact lt_irrefl 0 hp

theorem norm_sq_integrals_separate (u v : ℝ → H)
    (hu : Continuous u) (hv : Continuous v) (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖u x-v x‖^2) = 0) : u = v := by
  have h := norm_sq_integrals_separate_zero (fun x => u x-v x) (hu.sub hv) L hL hz
  funext x
  exact sub_eq_zero.mp (congrFun h x)

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem classical_difference_energy_conserved (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    (∫ x in b..b+L, ‖u s x-v s x‖^2) = ∫ x in b..b+L, ‖u t x-v t x‖^2 :=
  energy_eq (fun r x => u r x-v r x) (classical_sub_same_forcing u v hu hv) hV b s t

theorem classical_unique_at_time (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x))
    (s : ℝ) (hs : ∀ x, u s x = v s x) : u = v := by
  funext t
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  apply norm_sq_integrals_separate (u t) (v t)
    (hu.continuous_solution.comp hp) (hv.continuous_solution.comp hp) L hL
  intro b
  have h := classical_difference_energy_conserved u v hu hv hV b t s
  simpa [hs] using h

theorem classical_unique (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = v 0 x) : u = v :=
  classical_unique_at_time hL u v hu hv hV 0 h0

theorem classical_zero_of_time_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (s : ℝ) (hs : ∀ x, u s x = 0) : u = 0 :=
  classical_unique_at_time hL u 0 hu (classical_zero L V) hV s hs

theorem classical_zero_of_initial_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = 0) : u = 0 :=
  classical_zero_of_time_zero hL u hu hV 0 h0

end NDEAEvolve.Exp013


-- SOURCE lean/LegacyBridge.lean SHA256 145526a13ad87eb17d1de9f37b3e792e0ff2b725973a261237b9d1ebe2bc309e

/-! Exact specialization of the generic framework to the previously verified
spinor model, including its unique numerical limit. -/
noncomputable section
open Filter
open NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010 NDEAEvolve.Exp011
namespace NDEAEvolve.Exp013

def legacyPotential (_t _x : ℝ) : E 2 →L[ℂ] E 2 :=
  operatorOf (Exp007.Z + Exp007.X)

theorem legacyPotential_selfadjoint (t x : ℝ) :
    IsSelfAdjoint (legacyPotential t x) := Exp012.potential_selfadjoint

theorem legacy_classical_iff (u : ℝ → ℝ → E 2) :
    IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u ↔
      Exp010.IsClassicalPeriodicSolution u := by
  constructor
  · intro hu
    exact {
      time_differentiable := hu.time_differentiable
      space_differentiable := hu.space_differentiable
      second_space_differentiable := hu.second_space_differentiable
      continuous_solution := hu.continuous_solution
      continuous_time_derivative := hu.continuous_time_derivative
      continuous_space_derivative := hu.continuous_space_derivative
      continuous_second_derivative := hu.continuous_second_derivative
      periodic := hu.periodic
      schrodinger := fun t x => by simpa [legacyPotential] using hu.schrodinger t x }
  · intro hu
    exact {
      time_differentiable := hu.time_differentiable
      space_differentiable := hu.space_differentiable
      second_space_differentiable := hu.second_space_differentiable
      continuous_solution := hu.continuous_solution
      continuous_time_derivative := hu.continuous_time_derivative
      continuous_space_derivative := hu.continuous_space_derivative
      continuous_second_derivative := hu.continuous_second_derivative
      periodic := hu.periodic
      schrodinger := fun t x => by simpa [legacyPotential] using hu.schrodinger t x }

theorem legacy_unique_via_generic (u v : ℝ → ℝ → E 2)
    (hu : Exp010.IsClassicalPeriodicSolution u) (hv : Exp010.IsClassicalPeriodicSolution v)
    (s : ℝ) (hs : ∀ x, u s x = v s x) : u = v :=
  classical_unique_at_time (by positivity) u v
    ((legacy_classical_iff u).mpr hu) ((legacy_classical_iff v).mpr hv)
    legacyPotential_selfadjoint s hs

theorem legacy_eq_infiniteSolution (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : Exp010.IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x) : u = infiniteSolution a :=
  legacy_unique_via_generic u (infiniteSolution a) hu (infiniteSolution_classical a ha) 0 h0

theorem legacy_existsUnique_via_generic (a : ℤ → E 2) (ha : Regular a) :
    ∃! u : ℝ → ℝ → E 2,
      IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u ∧
      ∀ x, u 0 x = infiniteSolution a 0 x := by
  refine ⟨infiniteSolution a,
    ⟨(legacy_classical_iff _).mpr (infiniteSolution_classical a ha), fun _ => rfl⟩, ?_⟩
  intro u hu
  exact legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu.1) hu.2

theorem legacy_reconstruction_converges (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x) :
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => u p.1 p.2) atTop spaceTimeDomain := by
  rw [legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu) h0]
  exact reconstruction_tendstoUniformlyOn a ha

theorem legacy_reconstruction_error (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x)
    (t x : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖scheduledReconstruction q a t x - u t x‖ ≤ uniformBound q a := by
  rw [legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu) h0]
  exact scheduled_reconstruction_error_bound q a ha t x ht hx

end NDEAEvolve.Exp013


-- SOURCE lean/Controls.lean SHA256 0b297b21320d90c24c76d648666a2b3627bdbf6565c74eccb04205f41ddaf76d

/-! Exact examples exercise variable spatial potential, nonzero forcing,
and the positivity condition used by energy separation. -/
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp013.Controls

def profile (x : ℝ) : ℂ := ((2 + Real.sin x : ℝ) : ℂ)
def stationarySolution (_t x : ℝ) : ℂ := profile x
def spatialPotential (_t x : ℝ) : ℂ →L[ℂ] ℂ :=
  (((-Real.sin x / (2 + Real.sin x) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ ℂ

private theorem stationarySolution_slice (t : ℝ) : stationarySolution t = profile := rfl

private theorem profile_hasDerivAt (x : ℝ) :
    HasDerivAt profile ((Real.cos x : ℝ) : ℂ) x := by
  simpa only [profile] using! ((Real.hasDerivAt_sin x).const_add 2).ofReal_comp

private theorem profile_deriv (x : ℝ) : deriv profile x = (Real.cos x : ℂ) :=
  (profile_hasDerivAt x).deriv

private theorem profile_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv profile) ((-Real.sin x : ℝ) : ℂ) x := by
  rw [show deriv profile = (fun y : ℝ => (Real.cos y : ℂ)) from funext profile_deriv]
  exact (Real.hasDerivAt_cos x).ofReal_comp

private theorem profile_second_deriv (x : ℝ) :
    deriv (deriv profile) x = ((-Real.sin x : ℝ) : ℂ) :=
  (profile_second_hasDerivAt x).deriv

private theorem profile_denominator_ne_zero (x : ℝ) : 2 + Real.sin x ≠ 0 := by
  have h := Real.neg_one_le_sin x
  linarith

theorem spatialPotential_selfadjoint (t x : ℝ) : IsSelfAdjoint (spatialPotential t x) := by
  have hr : IsSelfAdjoint (((-Real.sin x / (2 + Real.sin x) : ℝ) : ℂ)) := by
    simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  exact hr.smul (IsSelfAdjoint.one (ℂ →L[ℂ] ℂ))

theorem spatialPotential_periodic (t : ℝ) :
    Function.Periodic (spatialPotential t) (2 * Real.pi) := by
  intro x
  simp [spatialPotential, Real.sin_add_two_pi]

theorem spatialPotential_continuous :
    Continuous (fun p : ℝ × ℝ => spatialPotential p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => -Real.sin p.2 / (2 + Real.sin p.2)) :=
    (Real.continuous_sin.comp continuous_snd).neg.div
      (continuous_const.add (Real.continuous_sin.comp continuous_snd))
      (fun p => profile_denominator_ne_zero p.2)
  exact (Complex.continuous_ofReal.comp h).smul continuous_const

theorem stationary_classical :
    IsClassicalPeriodicSolution (2 * Real.pi) spatialPotential 0 stationarySolution where
  time_differentiable t x := differentiableAt_const _
  space_differentiable t x := (profile_hasDerivAt x).differentiableAt
  second_space_differentiable t x := (profile_second_hasDerivAt x).differentiableAt
  continuous_solution := Complex.continuous_ofReal.comp
    (continuous_const.add (Real.continuous_sin.comp continuous_snd))
  continuous_time_derivative := by
    simpa only [stationarySolution, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_space_derivative := by
    simpa only [stationarySolution_slice, profile_deriv, Function.comp_def] using!
      (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))))
  continuous_second_derivative := by
    simpa only [stationarySolution_slice, profile_second_deriv, Function.comp_def] using!
      (Complex.continuous_ofReal.comp
        ((Real.continuous_sin.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))).neg))
  periodic t x := by simp [stationarySolution, profile, Real.sin_add_two_pi]
  schrodinger t x := by
    have hden := profile_denominator_ne_zero x
    simp only [stationarySolution_slice, deriv_const', profile_second_deriv,
      spatialPotential, _root_.smul_apply, ContinuousLinearMap.id_apply,
      Pi.zero_apply, add_zero, profile, smul_eq_mul]
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hden]
    simp

theorem stationary_nonzero (t x : ℝ) : stationarySolution t x ≠ 0 := by
  change ((2 + Real.sin x : ℝ) : ℂ) ≠ 0
  exact_mod_cast profile_denominator_ne_zero x

theorem stationary_nonconstant : stationarySolution 0 0 ≠ stationarySolution 0 (Real.pi / 2) := by
  norm_num [stationarySolution, profile, Real.sin_pi_div_two]

theorem spatialPotential_nonconstant : spatialPotential 0 0 ≠ spatialPotential 0 (Real.pi / 2) := by
  intro h
  have h1 := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  norm_num [spatialPotential, Real.sin_pi_div_two] at h1

theorem spatialPotential_active :
    spatialPotential 0 (Real.pi / 2) (stationarySolution 0 (Real.pi / 2)) = -1 := by
  norm_num [spatialPotential, stationarySolution, profile, Real.sin_pi_div_two]

def linearSolution (t _x : ℝ) : ℂ := (t : ℂ)
def constantForcing (_t _x : ℝ) : ℂ := Complex.I

private theorem linearSolution_slice (t : ℝ) :
    linearSolution t = (fun _ : ℝ => (t : ℂ)) := rfl

private theorem linear_time_derivative (t x : ℝ) :
    deriv (fun s => linearSolution s x) t = 1 := by
  simpa only [linearSolution, id_eq, Complex.ofReal_one] using!
    (hasDerivAt_id t).ofReal_comp.deriv

theorem forced_linear_classical (L : ℝ) :
    IsClassicalPeriodicSolution L 0 constantForcing linearSolution where
  time_differentiable t x := (hasDerivAt_id t).ofReal_comp.differentiableAt
  space_differentiable t x := differentiableAt_const _
  second_space_differentiable t x := by
    simpa only [linearSolution_slice, deriv_const'] using
      (differentiableAt_const (0 : ℂ) : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) x)
  continuous_solution := Complex.continuous_ofReal.comp continuous_fst
  continuous_time_derivative := by
    simpa only [linear_time_derivative] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℂ)))
  continuous_space_derivative := by
    simpa only [linearSolution_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_second_derivative := by
    simpa only [linearSolution_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  periodic t x := rfl
  schrodinger t x := by
    rw [linear_time_derivative]
    simp [linearSolution_slice, constantForcing]

theorem forcing_work_sign : forcingWork constantForcing linearSolution 1 0 = 2 := by
  norm_num [forcingWork, constantForcing, linearSolution, inner, RCLike.inner_apply]

theorem forcing_changes_norm : ‖linearSolution 0 0‖ ≠ ‖linearSolution 1 0‖ := by
  norm_num [linearSolution]

/-- Equal initial data and potential do not identify solutions when the
forcing differs. Both examples are classical on the same positive period. -/
theorem same_data_different_forcing :
    IsClassicalPeriodicSolution 1 0 constantForcing linearSolution ∧
      IsClassicalPeriodicSolution (H := ℂ) 1 0 0 0 ∧
      (∀ x : ℝ, linearSolution 0 x = 0) ∧ linearSolution 1 0 ≠ 0 := by
  refine ⟨forced_linear_classical 1, classical_zero 1 0, ?_, ?_⟩
  · intro x
    simp [linearSolution]
  · norm_num [linearSolution]

theorem zero_period_fails_separation :
    (∀ b : ℝ, (∫ _ in b..b+(0:ℝ), ‖(1 : ℂ)‖^2) = 0) ∧
      (fun _ : ℝ => (1 : ℂ)) ≠ 0 := by
  constructor
  · intro b
    simp
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

/-- The generic conservation theorem applies to the active variable potential. -/
theorem stationary_energy_conserved (b s t : ℝ) :
    energy stationarySolution b (2 * Real.pi) s =
      energy stationarySolution b (2 * Real.pi) t :=
  energy_eq stationarySolution stationary_classical spatialPotential_selfadjoint b s t

theorem stationary_unique (u : ℝ → ℝ → ℂ)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) spatialPotential 0 u)
    (s : ℝ) (hs : ∀ x, u s x = profile x) : u = stationarySolution :=
  classical_unique_at_time (by positivity) u stationarySolution hu stationary_classical
    spatialPotential_selfadjoint s hs

theorem forcing_work_eq (t x : ℝ) :
    forcingWork constantForcing linearSolution t x = 2 * t := by
  simp [forcingWork, constantForcing, linearSolution, smul_eq_mul, RCLike.inner_apply]

theorem forced_energy_formula (b L t : ℝ) :
    energy linearSolution b L t = L * t^2 := by
  simp [energy, linearSolution, smul_eq_mul, pow_two]
  ring

/-- The general work identity gives the actual derivative of the forced mass. -/
theorem forced_energy_derivative (b L t : ℝ) :
    HasDerivAt (energy linearSolution b L) (L * (2 * t)) t := by
  have hV : ∀ s x : ℝ, IsSelfAdjoint ((0 : ℝ → ℝ → ℂ →L[ℂ] ℂ) s x) := by
    intro s x
    exact IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)
  simpa [forcing_work_eq, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    energy_time_hasDerivAt_work linearSolution (forced_linear_classical L) hV b t

end NDEAEvolve.Exp013.Controls


#print axioms NDEAEvolve.Exp013.potential_cancellation
#print axioms NDEAEvolve.Exp013.imaginary_self_cancellation
#print axioms NDEAEvolve.Exp013.periodic_deriv
#print axioms NDEAEvolve.Exp013.density_time_hasDerivAt
#print axioms NDEAEvolve.Exp013.energyDensity_continuous
#print axioms NDEAEvolve.Exp013.densityDerivative_continuous
#print axioms NDEAEvolve.Exp013.fluxDerivative_continuous
#print axioms NDEAEvolve.Exp013.classical_time_derivative
#print axioms NDEAEvolve.Exp013.densityDerivative_eq_fluxDerivative_add_forcingWork
#print axioms NDEAEvolve.Exp013.forcingWork_continuous
#print axioms NDEAEvolve.Exp013.flux_hasDerivAt
#print axioms NDEAEvolve.Exp013.flux_periodic
#print axioms NDEAEvolve.Exp013.classical_sub_time_derivative
#print axioms NDEAEvolve.Exp013.classical_sub_space_derivative
#print axioms NDEAEvolve.Exp013.classical_sub_second_derivative
#print axioms NDEAEvolve.Exp013.classical_sub
#print axioms NDEAEvolve.Exp013.classical_sub_same_forcing
#print axioms NDEAEvolve.Exp013.classical_zero
#print axioms NDEAEvolve.Exp013.compact_derivative_bound
#print axioms NDEAEvolve.Exp013.joint_interval_hasDerivAt
#print axioms NDEAEvolve.Exp013.energy_intervalIntegrable
#print axioms NDEAEvolve.Exp013.densityDerivative_intervalIntegrable
#print axioms NDEAEvolve.Exp013.fluxDerivative_intervalIntegrable
#print axioms NDEAEvolve.Exp013.forcingWork_intervalIntegrable
#print axioms NDEAEvolve.Exp013.energy_time_hasDerivAt
#print axioms NDEAEvolve.Exp013.fluxDerivative_integral_zero
#print axioms NDEAEvolve.Exp013.densityDerivative_integral_eq_forcingWork
#print axioms NDEAEvolve.Exp013.energy_time_hasDerivAt_work
#print axioms NDEAEvolve.Exp013.energy_hasDerivAt_zero
#print axioms NDEAEvolve.Exp013.energy_eq
#print axioms NDEAEvolve.Exp013.energy_eq_initial
#print axioms NDEAEvolve.Exp013.norm_sq_integral_pos_of_ne_zero
#print axioms NDEAEvolve.Exp013.norm_sq_integrals_separate_zero
#print axioms NDEAEvolve.Exp013.norm_sq_integrals_separate
#print axioms NDEAEvolve.Exp013.classical_difference_energy_conserved
#print axioms NDEAEvolve.Exp013.classical_unique_at_time
#print axioms NDEAEvolve.Exp013.classical_unique
#print axioms NDEAEvolve.Exp013.classical_zero_of_time_zero
#print axioms NDEAEvolve.Exp013.classical_zero_of_initial_zero
#print axioms NDEAEvolve.Exp013.legacyPotential_selfadjoint
#print axioms NDEAEvolve.Exp013.legacy_classical_iff
#print axioms NDEAEvolve.Exp013.legacy_unique_via_generic
#print axioms NDEAEvolve.Exp013.legacy_eq_infiniteSolution
#print axioms NDEAEvolve.Exp013.legacy_existsUnique_via_generic
#print axioms NDEAEvolve.Exp013.legacy_reconstruction_converges
#print axioms NDEAEvolve.Exp013.legacy_reconstruction_error
#print axioms NDEAEvolve.Exp013.Controls.spatialPotential_selfadjoint
#print axioms NDEAEvolve.Exp013.Controls.spatialPotential_periodic
#print axioms NDEAEvolve.Exp013.Controls.spatialPotential_continuous
#print axioms NDEAEvolve.Exp013.Controls.stationary_classical
#print axioms NDEAEvolve.Exp013.Controls.stationary_nonzero
#print axioms NDEAEvolve.Exp013.Controls.stationary_nonconstant
#print axioms NDEAEvolve.Exp013.Controls.spatialPotential_nonconstant
#print axioms NDEAEvolve.Exp013.Controls.spatialPotential_active
#print axioms NDEAEvolve.Exp013.Controls.forced_linear_classical
#print axioms NDEAEvolve.Exp013.Controls.forcing_work_sign
#print axioms NDEAEvolve.Exp013.Controls.forcing_changes_norm
#print axioms NDEAEvolve.Exp013.Controls.same_data_different_forcing
#print axioms NDEAEvolve.Exp013.Controls.zero_period_fails_separation
#print axioms NDEAEvolve.Exp013.Controls.stationary_energy_conserved
#print axioms NDEAEvolve.Exp013.Controls.stationary_unique
#print axioms NDEAEvolve.Exp013.Controls.forcing_work_eq
#print axioms NDEAEvolve.Exp013.Controls.forced_energy_formula
#print axioms NDEAEvolve.Exp013.Controls.forced_energy_derivative
