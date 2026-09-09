/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/
import NDEAEvolve.Experiments.Exp002.OperatorCayley
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact adversarial witnesses for noncommutative Cayley composition

Each declaration below is a compiling positive witness: it proves that a corresponding
weakened or altered claim is false.  The examples use exact complex arithmetic.
-/

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace NDEAEvolve
namespace Exp002
namespace AdversarialWitnesses

abbrev Mat2 := Mat 2

def pauliX : Mat2 := !![0, 1; 1, 0]

def pauliZ : Mat2 := !![1, 0; 0, -1]

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

theorem pauli_generators_do_not_commute : ¬ Commute pauliX pauliZ := by
  intro h
  have h01 := congrFun (congrFun h.eq (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The actual Cayley factors retain the noncommutative ordering of the generators. -/
theorem pauli_cayley_factors_order_sensitive :
    cayley 1 pauliX * cayley 1 pauliZ ≠ cayley 1 pauliZ * cayley 1 pauliX := by
  intro h
  have hFactors : Commute (cayley 1 pauliX) (cayley 1 pauliZ) := h
  have hGenerators : Commute pauliX pauliZ :=
    (hermitian_cayley_commute_iff 1 1 pauliX pauliZ
      pauliX_hermitian pauliZ_hermitian (by norm_num)).mp hFactors
  exact pauli_generators_do_not_commute hGenerators

def pauliUX : Mat2 :=
  !![(3 : ℂ) / 5, -((4 : ℂ) / 5) * Complex.I;
     -((4 : ℂ) / 5) * Complex.I, (3 : ℂ) / 5]

def pauliUZ : Mat2 :=
  !![((5 : ℂ) - 12 * Complex.I) / 13, 0;
     0, ((5 : ℂ) + 12 * Complex.I) / 13]

theorem pauli_factors_order_sensitive : pauliUX * pauliUZ ≠ pauliUZ * pauliUX := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have hre := congrArg Complex.re h01
  norm_num [pauliUX, pauliUZ, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re] at hre

theorem pauli_commutator_wrong_sign :
    commutator pauliUX pauliUZ ≠ -commutator pauliUX pauliUZ := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have hre := congrArg Complex.re h01
  norm_num [commutator, pauliUX, pauliUZ, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.mul_re] at hre

/-- The wrong-sign control is tied to the actual Cayley factors, not only to
    separately tabulated matrices. -/
theorem pauli_cayley_commutator_wrong_sign :
    commutator (cayley 1 pauliX) (cayley 1 pauliZ) ≠
      -commutator (cayley 1 pauliX) (cayley 1 pauliZ) := by
  intro hSign
  have hTwice :
      (2 : ℂ) • commutator (cayley 1 pauliX) (cayley 1 pauliZ) = 0 := by
    rw [two_smul]
    calc
      commutator (cayley 1 pauliX) (cayley 1 pauliZ) +
          commutator (cayley 1 pauliX) (cayley 1 pauliZ) =
        commutator (cayley 1 pauliX) (cayley 1 pauliZ) +
          (-commutator (cayley 1 pauliX) (cayley 1 pauliZ)) :=
            congrArg
              (fun K : Mat2 =>
                commutator (cayley 1 pauliX) (cayley 1 pauliZ) + K)
              hSign
      _ = 0 := add_neg_cancel _
  have hZero : commutator (cayley 1 pauliX) (cayley 1 pauliZ) = 0 := by
    rcases smul_eq_zero.mp hTwice with hTwo | hZero
    · norm_num at hTwo
    · exact hZero
  have hCommute : Commute (cayley 1 pauliX) (cayley 1 pauliZ) :=
    (commutator_eq_zero_iff_commute _ _).mp hZero
  exact pauli_cayley_factors_order_sensitive hCommute.eq

def shearA : Mat2 := !![0, 1; 0, 0]

def shearR : Mat2 := !![1, -Complex.I; 0, 1]

def shearU : Mat2 := !![1, -2 * Complex.I; 0, 1]

theorem shearA_not_hermitian : ¬ shearA.IsHermitian := by
  intro h
  have h01 := h.apply (0 : Fin 2) (1 : Fin 2)
  norm_num [shearA] at h01

theorem shear_satisfies_cayley_update :
    cayleyD 1 shearA * shearU = cayleyN 1 shearA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyD, cayleyN, skewPart, cscalar, shearA, shearU,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]; ring

theorem shearR_eq_cayleyR : shearR = cayleyR 1 shearA := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyD, skewPart, cscalar, shearA, shearR, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem shear_cayley_eq : cayley 1 shearA = shearU := by
  unfold cayley
  rw [← shearR_eq_cayleyR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyN, skewPart, cscalar, shearA, shearR, shearU, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]; ring

theorem shearU_not_unitary : ¬ IsUnitary shearU := by
  intro h
  have h11 := congrFun (congrFun h.2 (1 : Fin 2)) (1 : Fin 2)
  norm_num [shearU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] at h11

/-- Dropping Hermiticity really permits a nonunitary Cayley transform. -/
theorem nonhermitian_cayley_not_unitary : ¬ IsUnitary (cayley 1 shearA) := by
  rw [shear_cayley_eq]
  exact shearU_not_unitary

def complexStepCayley (z : ℂ) : ℂ :=
  (1 - Complex.I * z) / (1 + Complex.I * z)

theorem complex_half_product :
    Complex.I * (Complex.I / 2) = (-1 : ℂ) / 2 := by
  calc
    Complex.I * (Complex.I / 2) = (Complex.I * Complex.I) / 2 := by ring
    _ = (-1 : ℂ) / 2 := by rw [Complex.I_mul_I]

theorem complex_step_half_eq_three :
    complexStepCayley (Complex.I / 2) = 3 := by
  simp [complexStepCayley, complex_half_product]
  norm_num

theorem complex_step_half_not_unitary :
    star (complexStepCayley (Complex.I / 2)) * complexStepCayley (Complex.I / 2) ≠ 1 := by
  rw [complex_step_half_eq_three]
  norm_num

def scalarCayley (a : ℝ) : ℂ :=
  (1 - Complex.I * (a : ℂ)) / (1 + Complex.I * (a : ℂ))

theorem scalarCayley_one : scalarCayley 1 = -Complex.I := by
  unfold scalarCayley
  apply (div_eq_iff ?_).2
  · ring_nf
    rw [Complex.I_sq]
    norm_num
    ring
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre

theorem scalarCayley_two : scalarCayley 2 = ((-3 : ℂ) - 4 * Complex.I) / 5 := by
  unfold scalarCayley
  apply (div_eq_iff ?_).2
  · field_simp
    ring_nf
    rw [Complex.I_sq]
    norm_num
    ring
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre

theorem false_semigroup_merging_witness :
    scalarCayley 1 * scalarCayley 1 ≠ scalarCayley 2 := by
  rw [scalarCayley_one, scalarCayley_two]
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.I_mul_I] at hre

theorem cayley_zero_step {n : ℕ} (A : Mat n) : cayley 0 A = 1 := by
  simp [cayley, cayleyN, cayleyR, cayleyD, skewPart, cscalar]

theorem zero_step_commutes {n : ℕ} (A B : Mat n) (β : ℝ) :
    Commute (cayley 0 A) (cayley β B) := by
  rw [cayley_zero_step]
  exact Commute.one_left _

theorem zero_step_breaks_commutation_iff :
    ¬(Commute (cayley 0 pauliX) (cayley 1 pauliZ) ↔ Commute pauliX pauliZ) := by
  intro h
  exact pauli_generators_do_not_commute (h.mp (zero_step_commutes pauliX pauliZ 1))

def nilA : Mat2 := !![0, 1; 0, 0]
def nilB : Mat2 := !![0, 0; 1, 0]
def nilRA : Mat2 := !![1, -Complex.I; 0, 1]
def nilRB : Mat2 := !![1, 0; -Complex.I, 1]
def nilK : Mat2 := !![1, 0; 0, -1]

theorem nilRA_eq_cayleyR : nilRA = cayleyR 1 nilA := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyD, skewPart, cscalar, nilA, nilRA, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem nilRB_eq_cayleyR : nilRB = cayleyR 1 nilB := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyD, skewPart, cscalar, nilB, nilRB, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem nilK_eq_commutator : nilK = commutator nilA nilB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, nilA, nilB, nilK, Matrix.mul_apply, Fin.sum_univ_two]

def correctInverseSandwich : Mat2 := nilRA * nilRB * nilK * nilRB * nilRA
def wrongLeftInverseSandwich : Mat2 := nilRB * nilRA * nilK * nilRB * nilRA

theorem nil_correct_inverse_sandwich : correctInverseSandwich = nilK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [correctInverseSandwich, nilRA, nilRB, nilK, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

theorem one_sided_inverse_permutation_detected :
    wrongLeftInverseSandwich ≠ correctInverseSandwich := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [wrongLeftInverseSandwich, correctInverseSandwich, nilRA, nilRB, nilK,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] at h00

/-- The same one-sided permutation failure, stated directly with the inverse
    factors and generator commutator used by `cayley_order_defect`. -/
theorem cayleyR_one_sided_inverse_permutation_detected :
    cayleyR 1 nilB * cayleyR 1 nilA * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA ≠
      cayleyR 1 nilA * cayleyR 1 nilB * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA := by
  rw [← nilRA_eq_cayleyR, ← nilRB_eq_cayleyR, ← nilK_eq_commutator]
  exact one_sided_inverse_permutation_detected

end AdversarialWitnesses
end Exp002
end NDEAEvolve
