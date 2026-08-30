import NDEAMathlibGate.CayleyEuclideanIsometryV1

/-! The inverse Cayley factor is the average of identity and the unitary update. -/

noncomputable section

namespace NDEAMathlibGate.CayleyInverseContractionV1

open Matrix Complex
open NDEAMathlibGate.CayleyEuclideanIsometryV1
open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR
open NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1

theorem cayleyR_average_matrix_identity {n : ℕ}
    (alpha : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    cayleyU alpha H (cayleyR alpha H) + 1 =
      (2 : ℂ) • cayleyR alpha H := by
  have hAR := cayleyA_mul_cayleyR alpha H hH
  calc
    cayleyU alpha H (cayleyR alpha H) + 1 =
        cayleyB alpha H * cayleyR alpha H +
          cayleyA alpha H * cayleyR alpha H := by
      rw [hAR]
      rfl
    _ = (cayleyB alpha H + cayleyA alpha H) * cayleyR alpha H := by
      rw [add_mul]
    _ = ((2 : ℂ) • (1 : CayleyEuclideanIsometryV1.Mat n)) * cayleyR alpha H := by
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [cayleyA, cayleyB, hij] <;> norm_num
    _ = (2 : ℂ) • cayleyR alpha H := by simp

theorem cayleyR_euclideanAction_average {n : ℕ}
    (alpha : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) (v : VecState n) :
    euclideanAction (cayleyR alpha H) v =
      (2 : ℝ)⁻¹ •
        (euclideanAction (cayleyU alpha H (cayleyR alpha H)) v + v) := by
  ext i
  have hm := congrArg
    (fun M : CayleyEuclideanIsometryV1.Mat n => M.mulVec (WithLp.ofLp v))
    (cayleyR_average_matrix_identity alpha H hH)
  have hi := congrFun hm i
  simp [euclideanAction, Matrix.add_mulVec, Matrix.smul_mulVec] at hi ⊢
  calc
    (cayleyR alpha H *ᵥ WithLp.ofLp v) i =
        (2 : ℂ)⁻¹ * (2 * (cayleyR alpha H *ᵥ WithLp.ofLp v) i) := by ring
    _ = (2 : ℂ)⁻¹ *
        ((cayleyU alpha H (cayleyR alpha H) *ᵥ WithLp.ofLp v) i +
          WithLp.ofLp v i) := by rw [← hi]
    _ = (2 : ℂ)⁻¹ *
          (cayleyU alpha H (cayleyR alpha H) *ᵥ WithLp.ofLp v) i +
        (2 : ℂ)⁻¹ * WithLp.ofLp v i := by ring

theorem cayleyR_euclideanAction_norm_le {n : ℕ}
    (alpha : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) (v : VecState n) :
    ‖euclideanAction (cayleyR alpha H) v‖ ≤ ‖v‖ := by
  rw [cayleyR_euclideanAction_average alpha H hH v]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
  calc
    (2 : ℝ)⁻¹ *
        ‖euclideanAction (cayleyU alpha H (cayleyR alpha H)) v + v‖ ≤
      (2 : ℝ)⁻¹ *
        (‖euclideanAction (cayleyU alpha H (cayleyR alpha H)) v‖ + ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = ‖v‖ := by
      rw [unitary_preserves_euclidean_norm]
      · ring
      · exact cayley_unitary_without_external_inverse alpha H hH

theorem cayleyR_weightedNorm_le {n : ℕ}
    (weight alpha : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) (v : VecState n) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm weight
        (euclideanAction (cayleyR alpha H) v) ≤
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm weight v := by
  unfold NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
  exact mul_le_mul_of_nonneg_left
    (cayleyR_euclideanAction_norm_le alpha H hH v) (Real.sqrt_nonneg weight)

def inverseContractionStatus : String :=
  "cayley_inverse_factor_nonexpansive_via_average_of_identity_and_unitary"

end NDEAMathlibGate.CayleyInverseContractionV1
