import Mathlib
import NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR

noncomputable section

open Matrix
open Complex

namespace NDEAMathlibGate
namespace CayleyTimeStepperFiniteStabilityV1R3

/-!
Finite/semi-discrete Cayley time-stepper stability bridge, v1R3.

Repair over V1R2:
  * keep explicit finite column adjoint,
  * prove preservation as a matrix equality first,
  * use `simp [Matrix.mul_assoc]` for the associativity bridge.

Scope:
  finite Matrix (Fin n) over ℂ;
  one-step finite update stability;
  Cayley specialization via CayleyUnitaryFiniteV2WrapperR;
  no broad continuous PDE theorem;
  no PML/operator theorem;
  no infinite-dimensional Hilbert-space theorem;
  no general-gauge theorem.
-/

abbrev Mat (n : Nat) :=
  NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.Mat n

abbrev State (n : Nat) :=
  Matrix (Fin n) (Fin 1) ℂ

abbrev Costate (n : Nat) :=
  Matrix (Fin 1) (Fin n) ℂ

/-- Finite matrix-vector action, represented as matrix-column multiplication. -/
def mvAction {n : Nat} (U : Mat n) (ψ : State n) : State n :=
  U * ψ

/-- Explicit adjoint of a finite column vector. -/
def adjointState {n : Nat} (ψ : State n) : Costate n :=
  fun _ i => star (ψ i 0)

/-- Complex scalar ψ†ψ. -/
def normSqC {n : Nat} (ψ : State n) : ℂ :=
  (adjointState ψ * ψ) 0 0

/-- Real finite squared ℓ² norm, as the real part of ψ†ψ. -/
def normSq {n : Nat} (ψ : State n) : ℝ :=
  (normSqC ψ).re

/--
Adjoint of Uψ is ψ†U†, with explicit column-adjoint.
-/
theorem adjoint_mvAction {n : Nat}
    (U : Mat n) (ψ : State n) :
    adjointState (mvAction U ψ) = adjointState ψ * star U := by
  ext i j
  fin_cases i
  simp [adjointState, mvAction, Matrix.mul_apply, star_sum, star_mul]

/--
Matrix-level preservation of ψ†ψ under star U * U = 1.
-/
theorem star_mul_self_preserves_inner_matrix {n : Nat}
    (U : Mat n) (ψ : State n)
    (hleft : star U * U = 1) :
    adjointState (mvAction U ψ) * mvAction U ψ =
      adjointState ψ * ψ := by
  calc
    adjointState (mvAction U ψ) * mvAction U ψ
        = (adjointState ψ * star U) * (U * ψ) := by
          rw [adjoint_mvAction U ψ]
          rfl
    _ = adjointState ψ * ((star U * U) * ψ) := by
          simp [Matrix.mul_assoc]
    _ = adjointState ψ * ((1 : Mat n) * ψ) := by
          rw [hleft]
    _ = adjointState ψ * ψ := by
          simp

/--
If star U * U = 1, then the complex scalar ψ†ψ is preserved by ψ ↦ Uψ.
-/
theorem star_mul_self_preserves_normSqC {n : Nat}
    (U : Mat n) (ψ : State n)
    (hleft : star U * U = 1) :
    normSqC (mvAction U ψ) = normSqC ψ := by
  unfold normSqC
  exact congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0)
    (star_mul_self_preserves_inner_matrix U ψ hleft)

/--
If star U * U = 1, then the real squared ℓ² norm is preserved by ψ ↦ Uψ.
-/
theorem star_mul_self_preserves_normSq {n : Nat}
    (U : Mat n) (ψ : State n)
    (hleft : star U * U = 1) :
    normSq (mvAction U ψ) = normSq ψ := by
  unfold normSq
  exact congrArg Complex.re (star_mul_self_preserves_normSqC U ψ hleft)

/--
Extract star U * U = 1 from the wrapper's IsUnitary predicate.

The wrapper currently defines IsUnitary U as:
  U * star U = 1 ∧ star U * U = 1.
-/
theorem star_mul_self_of_wrapper_unitary {n : Nat}
    (U : Mat n)
    (hU : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U) :
    star U * U = 1 := by
  unfold NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary at hU
  exact hU.2

/--
Unitary finite updates preserve the complex scalar ψ†ψ.
-/
theorem unitary_preserves_normSqC {n : Nat}
    (U : Mat n) (ψ : State n)
    (hU : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U) :
    normSqC (mvAction U ψ) = normSqC ψ := by
  exact star_mul_self_preserves_normSqC U ψ
    (star_mul_self_of_wrapper_unitary U hU)

/--
Unitary finite updates preserve the real finite squared ℓ² norm.
-/
theorem unitary_preserves_normSq {n : Nat}
    (U : Mat n) (ψ : State n)
    (hU : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U) :
    normSq (mvAction U ψ) = normSq ψ := by
  exact star_mul_self_preserves_normSq U ψ
    (star_mul_self_of_wrapper_unitary U hU)

/--
Cayley specialization.

If H is Hermitian, α is real, and R is a two-sided inverse of
A = I + i α H, then the Cayley time step preserves finite squared ℓ² norm.
-/
theorem cayley_update_preserves_normSq {n : Nat}
    (alpha : ℝ) (H R : Mat n) (ψ : State n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H * R = 1)
    (hRA :
      R * NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H = 1) :
    normSq
      (mvAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
        ψ)
      =
    normSq ψ := by
  exact unitary_preserves_normSq
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
    ψ
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayley_unitary_of_hermitian_and_inverse
      alpha H R hH hAR hRA)

/--
Complex scalar version of the Cayley specialization.
-/
theorem cayley_update_preserves_normSqC {n : Nat}
    (alpha : ℝ) (H R : Mat n) (ψ : State n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H * R = 1)
    (hRA :
      R * NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H = 1) :
    normSqC
      (mvAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
        ψ)
      =
    normSqC ψ := by
  exact unitary_preserves_normSqC
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
    ψ
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayley_unitary_of_hermitian_and_inverse
      alpha H R hH hAR hRA)

def finiteStabilityStatusV1R3 : String :=
  "finite_unitary_step_norm_preservation_validated"

def cayleyFiniteStabilityStatusV1R3 : String :=
  "cayley_finite_step_norm_preservation_validated"

def broadContinuousPDEClaimStatusV1R3 : String :=
  "not_claimed"

def pmlOperatorClaimStatusV1R3 : String :=
  "not_claimed"

def broadOperatorClaimStatusV1R3 : String :=
  "not_claimed"

def infiniteDimensionalHilbertClaimStatusV1R3 : String :=
  "not_claimed"

def generalGaugeClaimStatusV1R3 : String :=
  "not_claimed"

theorem true_finite_stability_status :
    finiteStabilityStatusV1R3 =
      "finite_unitary_step_norm_preservation_validated" := by
  rfl

theorem true_cayley_stability_status :
    cayleyFiniteStabilityStatusV1R3 =
      "cayley_finite_step_norm_preservation_validated" := by
  rfl

theorem true_broad_continuous_pde_not_claimed :
    broadContinuousPDEClaimStatusV1R3 = "not_claimed" := by
  rfl

theorem true_pml_operator_not_claimed :
    pmlOperatorClaimStatusV1R3 = "not_claimed" := by
  rfl

theorem true_broad_operator_not_claimed :
    broadOperatorClaimStatusV1R3 = "not_claimed" := by
  rfl

theorem true_infinite_dimensional_not_claimed :
    infiniteDimensionalHilbertClaimStatusV1R3 = "not_claimed" := by
  rfl

theorem true_general_gauge_not_claimed :
    generalGaugeClaimStatusV1R3 = "not_claimed" := by
  rfl

#check adjoint_mvAction
#check star_mul_self_preserves_inner_matrix
#check star_mul_self_preserves_normSqC
#check star_mul_self_preserves_normSq
#check unitary_preserves_normSqC
#check unitary_preserves_normSq
#check cayley_update_preserves_normSqC
#check cayley_update_preserves_normSq
#check true_finite_stability_status
#check true_broad_continuous_pde_not_claimed

end CayleyTimeStepperFiniteStabilityV1R3
end NDEAMathlibGate
