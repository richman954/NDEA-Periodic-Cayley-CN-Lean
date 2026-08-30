import NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1
import NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1

/-! Euclidean norm and distance preservation for finite unitary and Cayley actions. -/

noncomputable section

namespace NDEAMathlibGate.CayleyEuclideanIsometryV1

open Matrix

abbrev VecState (n : ℕ) :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.VecState n

abbrev Mat (n : ℕ) :=
  NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.Mat n

def euclideanAction {n : ℕ} (U : Mat n) (psi : VecState n) : VecState n :=
  WithLp.toLp 2 (U *ᵥ WithLp.ofLp psi)

theorem unitary_preserves_euclidean_norm {n : ℕ}
    (U : Mat n) (psi : VecState n)
    (hU : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U) :
    ‖euclideanAction U psi‖ = ‖psi‖ := by
  have hsq :=
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.unitary_preserves_normSq
      U (NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi) hU
  rw [NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.mvAction,
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.matrix_mul_toColumn] at hsq
  have hsq' : ‖euclideanAction U psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    calc
      ‖euclideanAction U psi‖ ^ 2 =
          NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
            (NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn
              (euclideanAction U psi)) :=
        (NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.v9_normSq_toColumn _).symm
      _ = NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
            (NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi) := hsq
      _ = ‖psi‖ ^ 2 :=
        NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.v9_normSq_toColumn _
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq'

theorem euclideanAction_sub {n : ℕ} (U : Mat n) (x y : VecState n) :
    euclideanAction U x - euclideanAction U y = euclideanAction U (x - y) := by
  ext i
  change (∑ j, U i j * WithLp.ofLp x j) -
      (∑ j, U i j * WithLp.ofLp y j) =
        ∑ j, U i j * (WithLp.ofLp x j - WithLp.ofLp y j)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem unitary_euclideanAction_isometry {n : ℕ}
    (U : Mat n)
    (hU : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary U) :
    ∀ x y : VecState n,
      ‖euclideanAction U x - euclideanAction U y‖ = ‖x - y‖ := by
  intro x y
  rw [euclideanAction_sub]
  exact unitary_preserves_euclidean_norm U (x - y) hU

theorem cayley_euclideanAction_isometry_without_external_inverse {n : ℕ}
    (alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    ∀ x y : VecState n,
      ‖euclideanAction
          (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
            (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H)) x -
        euclideanAction
          (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
            (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H)) y‖ =
        ‖x - y‖ :=
  unitary_euclideanAction_isometry _
    (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayley_unitary_without_external_inverse
      alpha H hH)

def cayleyEuclideanIsometryStatus : String :=
  "finite_cayley_euclidean_distance_preservation_validated"

end NDEAMathlibGate.CayleyEuclideanIsometryV1
