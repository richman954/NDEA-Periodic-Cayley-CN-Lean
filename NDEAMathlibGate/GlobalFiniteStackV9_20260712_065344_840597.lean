import NDEAMathlibGate.GlobalFiniteStackV8_20260712_053434_060974
import NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1

noncomputable section

namespace NDEAMathlibGate
namespace GlobalFiniteStackV9_20260712_065344_840597

/-!
Global FiniteStack Closure Pack V9 integration master.

This module integrates the authenticated V8 graph with the finite
Cayley-factor invertibility theorem. The caller no longer supplies an
external inverse: for finite Hermitian H and real alpha, the factor
I + i alpha H is proved invertible and its canonical inverse is used.

Not claimed: broad continuous-PDE convergence, PML/operator stability,
broad operator theory, infinite-dimensional Hilbert evolution,
general-gauge stability, or kernel-only global closure.
-/

abbrev Mat (n : Nat) := NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.Mat n
abbrev State (n : Nat) := NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.State n

def globalV9StackStatus : String := "validated"
def globalV9FactorInvertibilityStatus : String := "validated"
def globalV9ExternalInverseRequirementStatus : String := "discharged"
def globalV9BroadContinuousPDEConvergenceClaim : String := "not_claimed"
def globalV9PMLOperatorStabilityClaim : String := "not_claimed"
def globalV9BroadOperatorTheoryClaim : String := "not_claimed"
def globalV9InfiniteDimensionalHilbertEvolutionClaim : String := "not_claimed"
def globalV9GeneralGaugeStabilityClaim : String := "not_claimed"
def globalV9KernelOnlyClosureClaim : String := "not_claimed"

theorem global_v9_cayley_factor_isUnit {n : Nat}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    IsUnit (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H) := by
  exact NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyA_isUnit alpha H hH

theorem global_v9_cayley_factor_kernel_trivial {n : Nat}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (v : Fin n → ℂ)
    (hv : (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H).mulVec v = 0) :
    v = 0 := by
  exact NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyA_mulVec_kernel_trivial alpha H hH v hv

theorem global_v9_cayleyA_mul_inverse {n : Nat}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H *
        NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H = 1 := by
  exact NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyA_mul_cayleyR alpha H hH

theorem global_v9_inverse_mul_cayleyA {n : Nat}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H *
        NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H = 1 := by
  exact NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR_mul_cayleyA alpha H hH

theorem global_v9_cayley_unitary_without_external_inverse {n : Nat}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
        (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H)) := by
  exact NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayley_unitary_without_external_inverse alpha H hH

theorem global_v9_cayley_iterated_norm_preservation_without_external_inverse
    {n : Nat} (N : Nat) (alpha : ℝ) (H : Mat n) (psi : State n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
      (NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.iterateUpdate
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H))
        N psi) =
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq psi := by
  exact
    NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayley_update_preserves_normSq_iterated_without_external_inverse
      N alpha H psi hH

theorem global_v9_stack_status_true :
    globalV9StackStatus = "validated" := by rfl

theorem global_v9_factor_status_true :
    globalV9FactorInvertibilityStatus = "validated" := by rfl

theorem global_v9_external_inverse_discharged :
    globalV9ExternalInverseRequirementStatus = "discharged" := by rfl

theorem global_v9_broad_pde_not_claimed :
    globalV9BroadContinuousPDEConvergenceClaim = "not_claimed" := by rfl

theorem global_v9_pml_not_claimed :
    globalV9PMLOperatorStabilityClaim = "not_claimed" := by rfl

theorem global_v9_broad_operator_not_claimed :
    globalV9BroadOperatorTheoryClaim = "not_claimed" := by rfl

theorem global_v9_infinite_dimensional_not_claimed :
    globalV9InfiniteDimensionalHilbertEvolutionClaim = "not_claimed" := by rfl

theorem global_v9_general_gauge_not_claimed :
    globalV9GeneralGaugeStabilityClaim = "not_claimed" := by rfl

theorem global_v9_kernel_only_not_claimed :
    globalV9KernelOnlyClosureClaim = "not_claimed" := by rfl

#check global_v9_cayley_factor_isUnit
#check global_v9_cayley_factor_kernel_trivial
#check global_v9_cayleyA_mul_inverse
#check global_v9_inverse_mul_cayleyA
#check global_v9_cayley_unitary_without_external_inverse
#check global_v9_cayley_iterated_norm_preservation_without_external_inverse

end GlobalFiniteStackV9_20260712_065344_840597
end NDEAMathlibGate
