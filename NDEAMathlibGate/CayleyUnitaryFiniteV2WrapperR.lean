import Mathlib
import NDEAMathlibGate.CayleyUnitaryStarRingV2

noncomputable section

open Matrix
open Complex
open NDEAMathlibGate.CayleyUnitaryStarRingV2

namespace NDEAMathlibGate
namespace CayleyUnitaryFiniteV2WrapperR

/-!
Finite-Matrix Cayley Unitarity Wrapper.

Specializes `cayley_unitary_star_ring` to finite complex matrices, bridging
the Hermitian and scalar identities to the abstract StarRing requirement.
-/

abbrev Mat (n : Nat) := Matrix (Fin n) (Fin n) ℂ

def IsHermitian {n : Nat} (H : Mat n) : Prop := star H = H

def IsUnitary {n : Nat} (U : Mat n) : Prop :=
  U * star U = 1 ∧ star U * U = 1

def cscalar (alpha : ℝ) : ℂ := Complex.I * (alpha : ℂ)

def cayleyA {n : Nat} (alpha : ℝ) (H : Mat n) : Mat n := 1 + (cscalar alpha) • H
def cayleyB {n : Nat} (alpha : ℝ) (H : Mat n) : Mat n := 1 - (cscalar alpha) • H

def cayleyU {n : Nat} (alpha : ℝ) (H R : Mat n) : Mat n := cayleyB alpha H * R

theorem star_cscalar (alpha : ℝ) : star (cscalar alpha) = - cscalar alpha := by
  apply Complex.ext <;> simp [cscalar]

theorem cayleyA_star {n : Nat} (alpha : ℝ) (H : Mat n) (hH : IsHermitian H) :
    star (cayleyA alpha H) = cayleyB alpha H := by
  unfold IsHermitian at hH
  simp [cayleyA, cayleyB, star_smul, star_cscalar, hH, sub_eq_add_neg]

theorem cayleyA_normal {n : Nat} (alpha : ℝ) (H : Mat n) (hH : IsHermitian H) :
    cayleyA alpha H * star (cayleyA alpha H) = star (cayleyA alpha H) * cayleyA alpha H := by
  rw [cayleyA_star alpha H hH]
  unfold cayleyA cayleyB
  set Z : Mat n := cscalar alpha • H
  noncomm_ring

/-- Main theorem delegating finite matrix unitarity to the abstract StarRing core. -/
theorem cayley_unitary_of_hermitian_and_inverse {n : Nat}
    (alpha : ℝ) (H R : Mat n)
    (hH : IsHermitian H)
    (hAR : cayleyA alpha H * R = 1)
    (hRA : R * cayleyA alpha H = 1) :
    IsUnitary (cayleyU alpha H R) := by
  unfold cayleyU
  have h_star := cayleyA_star alpha H hH
  rw [← h_star]
  have h_norm := cayleyA_normal alpha H hH
  exact cayley_unitary_star_ring (cayleyA alpha H) R h_norm hAR hRA

def finiteCayleyWrapperStatus : String := "finite_matrix_wrapper_validated"
def broadOperatorClaimStatusWrapper : String := "not_claimed"

end CayleyUnitaryFiniteV2WrapperR
end NDEAMathlibGate
