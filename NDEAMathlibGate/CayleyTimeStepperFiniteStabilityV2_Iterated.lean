import Mathlib
import NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3

noncomputable section

namespace NDEAMathlibGate
namespace CayleyTimeStepperFiniteStabilityV2_Iterated

/-!
Cayley time-stepper finite stability v2: arbitrary finite iteration.

This module extends the verified one-step result from
CayleyTimeStepperFiniteStabilityV1R3.

For a fixed finite matrix U, `iterateUpdate U N ψ` applies the update
ψ ↦ Uψ exactly N times.

The main theorem proves that if U is unitary, the finite squared
inner-product norm is preserved for every N : Nat. A second theorem
specializes the result to the finite Cayley update.

Scope:
  * finite matrices Matrix (Fin n) (Fin n) ℂ;
  * finite column states Matrix (Fin n) (Fin 1) ℂ;
  * arbitrary finite natural-number step count;
  * exact norm preservation;
  * no continuous-PDE convergence theorem;
  * no PML/operator stability theorem;
  * no broad operator theorem;
  * no infinite-dimensional Hilbert theorem;
  * no general-gauge stability theorem;
  * no kernel-only closure claim.
-/

abbrev Mat (n : Nat) :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.Mat n

abbrev State (n : Nat) :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.State n

abbrev mvAction {n : Nat}
    (U : Mat n) (ψ : State n) : State n :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.mvAction U ψ

abbrev normSqC {n : Nat} (ψ : State n) : ℂ :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.normSqC ψ

abbrev normSq {n : Nat} (ψ : State n) : ℝ :=
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.normSq ψ

/--
Apply the fixed update U exactly N times to ψ.
-/
def iterateUpdate {n : Nat} (U : Mat n) :
    Nat → State n → State n
  | 0, ψ => ψ
  | Nat.succ k, ψ => mvAction U (iterateUpdate U k ψ)

@[simp]
theorem iterateUpdate_zero {n : Nat}
    (U : Mat n) (ψ : State n) :
    iterateUpdate U 0 ψ = ψ := by
  rfl

@[simp]
theorem iterateUpdate_succ {n : Nat}
    (U : Mat n) (N : Nat) (ψ : State n) :
    iterateUpdate U (Nat.succ N) ψ =
      mvAction U (iterateUpdate U N ψ) := by
  rfl

/--
A unitary finite update preserves the complex scalar normSqC
for every finite iteration count N.
-/
theorem unitary_preserves_normSqC_iterated {n : Nat}
    (U : Mat n)
    (ψ : State n)
    (hU :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U)
    (N : Nat) :
    normSqC (iterateUpdate U N ψ) = normSqC ψ := by
  induction N with
  | zero =>
      rfl
  | succ N ih =>
      calc
        normSqC (iterateUpdate U (Nat.succ N) ψ)
            =
          normSqC
            (mvAction U (iterateUpdate U N ψ)) := by
              rfl
        _ =
          normSqC (iterateUpdate U N ψ) := by
            exact
              NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.unitary_preserves_normSqC
                U
                (iterateUpdate U N ψ)
                hU
        _ = normSqC ψ := ih

/--
A unitary finite update preserves the real finite squared ℓ² norm
for every finite iteration count N.
-/
theorem unitary_preserves_normSq_iterated {n : Nat}
    (U : Mat n)
    (ψ : State n)
    (hU :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U)
    (N : Nat) :
    normSq (iterateUpdate U N ψ) = normSq ψ := by
  induction N with
  | zero =>
      rfl
  | succ N ih =>
      calc
        normSq (iterateUpdate U (Nat.succ N) ψ)
            =
          normSq
            (mvAction U (iterateUpdate U N ψ)) := by
              rfl
        _ =
          normSq (iterateUpdate U N ψ) := by
            exact
              NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.unitary_preserves_normSq
                U
                (iterateUpdate U N ψ)
                hU
        _ = normSq ψ := ih

/--
Finite Cayley specialization for arbitrary finite step count.

If H is Hermitian and R is a two-sided inverse of I + i α H,
then iterating the Cayley update N times preserves normSq.
-/
theorem cayley_update_preserves_normSq_iterated {n : Nat}
    (N : Nat)
    (alpha : ℝ)
    (H R : Mat n)
    (ψ : State n)
    (hH :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H * R = 1)
    (hRA :
      R * NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H = 1) :
    normSq
      (iterateUpdate
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
        N
        ψ)
      =
    normSq ψ := by
  have hU :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R) :=
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayley_unitary_of_hermitian_and_inverse
      alpha H R hH hAR hRA

  exact
    unitary_preserves_normSq_iterated
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
      ψ
      hU
      N

/--
Complex-scalar version of arbitrary finite-step Cayley preservation.
-/
theorem cayley_update_preserves_normSqC_iterated {n : Nat}
    (N : Nat)
    (alpha : ℝ)
    (H R : Mat n)
    (ψ : State n)
    (hH :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (hAR :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H * R = 1)
    (hRA :
      R * NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA alpha H = 1) :
    normSqC
      (iterateUpdate
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
        N
        ψ)
      =
    normSqC ψ := by
  have hU :
      NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R) :=
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayley_unitary_of_hermitian_and_inverse
      alpha H R hH hAR hRA

  exact
    unitary_preserves_normSqC_iterated
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H R)
      ψ
      hU
      N

def iteratedFiniteStabilityStatusV2 : String :=
  "arbitrary_finite_step_unitary_norm_preservation_validated"

def iteratedCayleyStabilityStatusV2 : String :=
  "arbitrary_finite_step_cayley_norm_preservation_validated"

def broadContinuousPDEConvergenceClaimStatusV2 : String :=
  "not_claimed"

def pmlOperatorStabilityClaimStatusV2 : String :=
  "not_claimed"

def broadOperatorTheoryClaimStatusV2 : String :=
  "not_claimed"

def infiniteDimensionalHilbertEvolutionClaimStatusV2 : String :=
  "not_claimed"

def generalGaugeStabilityClaimStatusV2 : String :=
  "not_claimed"

def kernelOnlyClosureClaimStatusV2 : String :=
  "not_claimed"

theorem true_iterated_finite_stability_status :
    iteratedFiniteStabilityStatusV2 =
      "arbitrary_finite_step_unitary_norm_preservation_validated" := by
  rfl

theorem true_iterated_cayley_stability_status :
    iteratedCayleyStabilityStatusV2 =
      "arbitrary_finite_step_cayley_norm_preservation_validated" := by
  rfl

theorem true_broad_pde_convergence_not_claimed :
    broadContinuousPDEConvergenceClaimStatusV2 =
      "not_claimed" := by
  rfl

theorem true_pml_stability_not_claimed :
    pmlOperatorStabilityClaimStatusV2 =
      "not_claimed" := by
  rfl

theorem true_broad_operator_not_claimed :
    broadOperatorTheoryClaimStatusV2 =
      "not_claimed" := by
  rfl

theorem true_infinite_dimensional_not_claimed :
    infiniteDimensionalHilbertEvolutionClaimStatusV2 =
      "not_claimed" := by
  rfl

theorem true_general_gauge_not_claimed :
    generalGaugeStabilityClaimStatusV2 =
      "not_claimed" := by
  rfl

theorem true_kernel_only_not_claimed :
    kernelOnlyClosureClaimStatusV2 =
      "not_claimed" := by
  rfl

#check iterateUpdate
#check unitary_preserves_normSqC_iterated
#check unitary_preserves_normSq_iterated
#check cayley_update_preserves_normSqC_iterated
#check cayley_update_preserves_normSq_iterated
#check true_iterated_finite_stability_status
#check true_broad_pde_convergence_not_claimed

end CayleyTimeStepperFiniteStabilityV2_Iterated
end NDEAMathlibGate
