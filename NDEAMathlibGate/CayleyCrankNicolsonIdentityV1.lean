import NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1

/-! Exact Crank--Nicolson identities for the finite Cayley update. -/

noncomputable section

open Matrix Complex

namespace NDEAMathlibGate.CayleyCrankNicolsonIdentityV1

open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR
open NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Vec (n : ℕ) := Fin n → ℂ

theorem cayleyA_mul_cayleyU_eq_cayleyB
    {n : ℕ} (alpha : ℝ) (H R : Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR : cayleyA alpha H * R = 1) :
    cayleyA alpha H * cayleyU alpha H R = cayleyB alpha H := by
  have hcomm := cayleyA_normal alpha H hH
  rw [cayleyA_star alpha H hH] at hcomm
  unfold cayleyU
  calc
    cayleyA alpha H * (cayleyB alpha H * R) =
        (cayleyA alpha H * cayleyB alpha H) * R := by rw [mul_assoc]
    _ = (cayleyB alpha H * cayleyA alpha H) * R := by rw [hcomm]
    _ = cayleyB alpha H * (cayleyA alpha H * R) := by rw [mul_assoc]
    _ = cayleyB alpha H := by rw [hAR, mul_one]

theorem cayley_state_factor_equation
    {n : ℕ} (alpha : ℝ) (H R : Mat n) (psi : Vec n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR : cayleyA alpha H * R = 1) :
    (cayleyA alpha H).mulVec ((cayleyU alpha H R).mulVec psi) =
      (cayleyB alpha H).mulVec psi := by
  rw [Matrix.mulVec_mulVec]
  rw [cayleyA_mul_cayleyU_eq_cayleyB alpha H R hH hAR]

theorem cayley_state_midpoint_equation
    {n : ℕ} (alpha : ℝ) (H R : Mat n) (psi : Vec n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR : cayleyA alpha H * R = 1) :
    (cayleyU alpha H R).mulVec psi - psi =
      -(cscalar alpha) •
        H.mulVec ((cayleyU alpha H R).mulVec psi + psi) := by
  have hfactor := cayley_state_factor_equation alpha H R psi hH hAR
  rw [cayleyA, cayleyB] at hfactor
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec] at hfactor
  ext i
  have hi := congrFun hfactor i
  rw [Matrix.mulVec_add]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.one_mulVec, Matrix.smul_mulVec] at hi ⊢
  linear_combination hi

theorem canonical_cayley_state_midpoint_equation
    {n : ℕ} (alpha : ℝ) (H : Mat n) (psi : Vec n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    (cayleyU alpha H (cayleyR alpha H)).mulVec psi - psi =
      -(cscalar alpha) •
        H.mulVec ((cayleyU alpha H (cayleyR alpha H)).mulVec psi + psi) := by
  exact cayley_state_midpoint_equation alpha H (cayleyR alpha H) psi hH
    (cayleyA_mul_cayleyR alpha H hH)

def crankNicolsonIdentityStatus : String :=
  "finite_cayley_exact_crank_nicolson_midpoint_identity_validated"

theorem crankNicolsonIdentityStatus_true :
    crankNicolsonIdentityStatus =
      "finite_cayley_exact_crank_nicolson_midpoint_identity_validated" := rfl

end NDEAMathlibGate.CayleyCrankNicolsonIdentityV1
