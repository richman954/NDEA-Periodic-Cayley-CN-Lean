import Mathlib
import NDEAMathlibGate.GlobalFiniteStackV8_20260712_053434_060974

noncomputable section

open Matrix
open Complex
open scoped ComplexOrder

namespace NDEAMathlibGate
namespace CayleyFactorInvertibilityFiniteV1

/-!
Finite Cayley-factor invertibility.

For

  A = I + i α H

with finite complex H, real α, and Hermitian H, this module proves that
A is invertible.

The central Gram identity is

  A* A = I + B* B

where B = i α H.

The right-hand side is positive definite because I is positive definite
and B*B is positive semidefinite.
-/

abbrev Mat (n : Nat) :=
  NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.Mat n

abbrev State (n : Nat) :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.State n

/-- The skew-adjoint part i α H. -/
def skewPart {n : Nat}
    (alpha : ℝ) (H : Mat n) : Mat n :=
  NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cscalar alpha • H

/-- Hermitian H and real α make i α H skew-adjoint. -/
theorem skewPart_star {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    star (skewPart alpha H) =
      -skewPart alpha H := by
  unfold skewPart
  unfold NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian at hH
  simp [
    star_smul,
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.star_cscalar,
    hH
  ]

/--
The Cayley factor Gram matrix is identity plus a Gram square.
-/
theorem cayleyA_gram_eq {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    star (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) *
        NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H
      =
    1 + star (skewPart alpha H) *
      skewPart alpha H := by
  rw [NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA_star alpha H hH]

  change
    (1 - skewPart alpha H) *
        (1 + skewPart alpha H)
      =
    1 + star (skewPart alpha H) *
      skewPart alpha H

  rw [skewPart_star alpha H hH]
  noncomm_ring

/--
The Cayley-factor Gram matrix is positive definite.
-/
theorem cayleyA_gram_posDef {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    Matrix.PosDef
      (star (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) *
        NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) := by
  rw [cayleyA_gram_eq alpha H hH]

  have hOne :
      Matrix.PosDef (1 : Mat n) :=
    Matrix.PosDef.one

  have hGram :
      Matrix.PosSemidef
        (star (skewPart alpha H) *
          skewPart alpha H) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.posSemidef_conjTranspose_mul_self
        (skewPart alpha H))

  exact hOne.add_posSemidef hGram

/--
The finite Cayley factor I + i α H is a unit.
-/
theorem cayleyA_isUnit {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    IsUnit (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) :=
by
  let A : Mat n := NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H

  have hGramUnit : IsUnit (star A * A) := by
    simpa [A] using
      (cayleyA_gram_posDef alpha H hH).isUnit

  have hGramInjective :
      Function.Injective (star A * A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hGramUnit

  have hAInjective : Function.Injective A.mulVec := by
    intro x y hxy
    apply hGramInjective
    simpa only [Matrix.mulVec_mulVec] using
      congrArg (fun z => (star A).mulVec z) hxy

  have hAUnit : IsUnit A :=
    Matrix.mulVec_injective_iff_isUnit.mp hAInjective

  simpa [A] using hAUnit

/--
The Cayley factor has nonzero/unit determinant.
-/
theorem cayleyA_det_isUnit {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    IsUnit (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H).det := by
  exact
    (Matrix.isUnit_iff_isUnit_det
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)).mp
      (cayleyA_isUnit alpha H hH)

/--
The finite Cayley factor has trivial mulVec kernel.
-/
theorem cayleyA_mulVec_kernel_trivial {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (v : Fin n → ℂ)
    (hv :
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H).mulVec v = 0) :
    v = 0 := by
  have hInjective :
      Function.Injective
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (cayleyA_isUnit alpha H hH)

  apply hInjective
  simpa using hv

def factorInvertibilityStatusV1 : String :=
  "finite_hermitian_cayley_factor_invertibility_validated"

def kernelTrivialityStatusV1 : String :=
  "finite_cayley_factor_kernel_triviality_validated"

def broadContinuousPDEConvergenceClaimStatusV1 : String :=
  "not_claimed"

def pmlOperatorStabilityClaimStatusV1 : String :=
  "not_claimed"

def broadOperatorTheoryClaimStatusV1 : String :=
  "not_claimed"

def infiniteDimensionalHilbertEvolutionClaimStatusV1 : String :=
  "not_claimed"

def generalGaugeStabilityClaimStatusV1 : String :=
  "not_claimed"

def kernelOnlyClosureClaimStatusV1 : String :=
  "not_claimed"

theorem true_factor_invertibility_status :
    factorInvertibilityStatusV1 =
      "finite_hermitian_cayley_factor_invertibility_validated" := by
  rfl

theorem true_kernel_triviality_status :
    kernelTrivialityStatusV1 =
      "finite_cayley_factor_kernel_triviality_validated" := by
  rfl


/-- Canonical nonsingular inverse of I + i α H. -/
def cayleyR {n : Nat}
    (alpha : ℝ)
    (H : Mat n) : Mat n :=
  (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)⁻¹

/--
An explicit `Invertible` witness for the finite Cayley factor.
-/
noncomputable def cayleyAInvertible {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    Invertible (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) :=
  Matrix.invertibleOfIsUnitDet
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)
    (cayleyA_det_isUnit alpha H hH)

/-- Right-inverse law. -/
theorem cayleyA_mul_cayleyR {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H *
        cayleyR alpha H
      =
    1 := by
  change
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H *
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)⁻¹
      =
    1

  exact
    Matrix.mul_nonsing_inv
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)
      (cayleyA_det_isUnit alpha H hH)

/-- Left-inverse law. -/
theorem cayleyR_mul_cayleyA {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    cayleyR alpha H *
        NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H
      =
    1 := by
  change
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)⁻¹ *
        NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H
      =
    1

  exact
    Matrix.nonsing_inv_mul
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H)
      (cayleyA_det_isUnit alpha H hH)

/--
Finite Cayley unitarity without an externally supplied inverse.
-/
theorem cayley_unitary_without_external_inverse {n : Nat}
    (alpha : ℝ)
    (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
        alpha
        H
        (cayleyR alpha H)) := by
  exact
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayley_unitary_of_hermitian_and_inverse
      alpha
      H
      (cayleyR alpha H)
      hH
      (cayleyA_mul_cayleyR alpha H hH)
      (cayleyR_mul_cayleyA alpha H hH)

/--
Arbitrary finite-step Cayley norm preservation without an externally
supplied inverse.
-/
theorem cayley_update_preserves_normSq_iterated_without_external_inverse
    {n : Nat}
    (N : Nat)
    (alpha : ℝ)
    (H : Mat n)
    (psi : State n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
      (NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.iterateUpdate
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
          alpha
          H
          (cayleyR alpha H))
        N
        psi)
      =
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq psi := by
  exact
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.cayley_update_preserves_normSq_iterated
      N
      alpha
      H
      (cayleyR alpha H)
      psi
      hH
      (cayleyA_mul_cayleyR alpha H hH)
      (cayleyR_mul_cayleyA alpha H hH)

/--
Complex-scalar version of arbitrary finite-step preservation.
-/
theorem cayley_update_preserves_normSqC_iterated_without_external_inverse
    {n : Nat}
    (N : Nat)
    (alpha : ℝ)
    (H : Mat n)
    (psi : State n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSqC
      (NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.iterateUpdate
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
          alpha
          H
          (cayleyR alpha H))
        N
        psi)
      =
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSqC psi := by
  exact
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.cayley_update_preserves_normSqC_iterated
      N
      alpha
      H
      (cayleyR alpha H)
      psi
      hH
      (cayleyA_mul_cayleyR alpha H hH)
      (cayleyR_mul_cayleyA alpha H hH)

def twoSidedInverseStatusV1 : String :=
  "canonical_two_sided_inverse_validated"

def unconditionalFiniteCayleyUnitarityStatusV1 : String :=
  "finite_cayley_unitarity_without_external_inverse_validated"

def unconditionalIteratedStabilityStatusV1 : String :=
  "arbitrary_finite_step_stability_without_external_inverse_validated"

theorem true_two_sided_inverse_status :
    twoSidedInverseStatusV1 =
      "canonical_two_sided_inverse_validated" := by
  rfl

theorem true_unconditional_unitarity_status :
    unconditionalFiniteCayleyUnitarityStatusV1 =
      "finite_cayley_unitarity_without_external_inverse_validated" := by
  rfl

theorem true_unconditional_iterated_status :
    unconditionalIteratedStabilityStatusV1 =
      "arbitrary_finite_step_stability_without_external_inverse_validated" := by
  rfl

#check cayleyA_gram_posDef
#check cayleyA_isUnit
#check cayleyA_mulVec_kernel_trivial
#check cayleyA_mul_cayleyR
#check cayleyR_mul_cayleyA
#check cayley_unitary_without_external_inverse
#check cayley_update_preserves_normSq_iterated_without_external_inverse

end CayleyFactorInvertibilityFiniteV1
end NDEAMathlibGate
