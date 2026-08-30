import Mathlib.Algebra.Star.Basic

namespace NDEAMathlibGate
namespace CayleyUnitaryStarRingV2

/-!
Abstract StarRing Cayley Unitarity.

By abstracting to a StarRing, we avoid Matrix namespace collisions and
reduce the proof to pure non-commutative star-algebra over `R`.

If A is normal (`A * star A = star A * A`) and `invA` is a two-sided
inverse, then `(star A * invA)` is unitary.
-/

theorem cayley_unitary_star_ring {R : Type*} [Ring R] [StarRing R] (A invA : R)
    (h_norm : A * star A = star A * A)
    (h_inv1 : A * invA = 1)
    (h_inv2 : invA * A = 1) :
    (star A * invA) * star (star A * invA) = 1 ∧ star (star A * invA) * (star A * invA) = 1 := by
  
  -- Lemma: invA commutes with star A
  have h_comm : invA * star A = star A * invA := by
    calc
      invA * star A = invA * star A * 1 := by rw [mul_one]
      _ = invA * star A * (A * invA) := by rw [← h_inv1]
      _ = invA * (star A * A) * invA := by simp only [mul_assoc]
      _ = invA * (A * star A) * invA := by rw [← h_norm]
      _ = (invA * A) * star A * invA := by simp only [← mul_assoc]
      _ = 1 * star A * invA := by rw [h_inv2]
      _ = star A * invA := by rw [one_mul]

  have hUU_star : (star A * invA) * star (star A * invA) = 1 := by
    calc
      (star A * invA) * star (star A * invA)
        = (star A * invA) * (star invA * A) := by rw [star_mul, star_star]
      _ = (star A * invA) * star invA * A := by simp only [mul_assoc]
      _ = (invA * star A) * star invA * A := by rw [← h_comm]
      _ = invA * (star A * star invA) * A := by simp only [mul_assoc]
      _ = invA * star (invA * A) * A := by rw [← star_mul]
      _ = invA * star 1 * A := by rw [h_inv2]
      _ = invA * 1 * A := by rw [star_one]
      _ = invA * A := by rw [mul_one]
      _ = 1 := h_inv2

  have hStar_UU : star (star A * invA) * (star A * invA) = 1 := by
    calc
      star (star A * invA) * (star A * invA)
        = (star invA * A) * (star A * invA) := by rw [star_mul, star_star]
      _ = star invA * (A * star A) * invA := by simp only [mul_assoc]
      _ = star invA * (star A * A) * invA := by rw [h_norm]
      _ = (star invA * star A) * (A * invA) := by simp only [mul_assoc]
      _ = star (A * invA) * (A * invA) := by rw [← star_mul]
      _ = star 1 * 1 := by rw [h_inv1]
      _ = 1 * 1 := by rw [star_one]
      _ = 1 := mul_one 1

  exact ⟨hUU_star, hStar_UU⟩

def cayleyUnitaryStarRingV2Status : String :=
  "star_ring_cayley_unitarity_validated"

def broadOperatorClaimStatusV2 : String :=
  "not_claimed"

def pmlClaimStatusV2 : String :=
  "not_claimed"

def infiniteDimensionalClaimStatusV2 : String :=
  "not_claimed"

end CayleyUnitaryStarRingV2
end NDEAMathlibGate
