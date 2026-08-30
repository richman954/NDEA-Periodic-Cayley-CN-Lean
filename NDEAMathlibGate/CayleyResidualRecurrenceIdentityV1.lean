import NDEAMathlibGate.CayleyInverseContractionV1
import NDEAMathlibGate.PeriodicCayleyScaledDefectV1

/-! Exact conversion of a Crank--Nicolson factor residual to Cayley recurrence form. -/

noncomputable section

namespace NDEAMathlibGate.CayleyResidualRecurrenceIdentityV1

open Matrix Complex
open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR
open NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1
open NDEAMathlibGate.CayleyEuclideanIsometryV1

theorem cayleyR_mul_cayleyB_eq_cayleyU {n : ℕ}
    (alpha : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H) :
    cayleyR alpha H * cayleyB alpha H =
      cayleyU alpha H (cayleyR alpha H) := by
  have hRA := cayleyR_mul_cayleyA alpha H hH
  have hAR := cayleyA_mul_cayleyR alpha H hH
  have hB : cayleyB alpha H =
      (2 : ℂ) • (1 : CayleyEuclideanIsometryV1.Mat n) - cayleyA alpha H := by
    ext i j
    by_cases hij : i = j <;> simp [cayleyA, cayleyB, hij] <;> ring
  unfold cayleyU
  rw [hB]
  noncomm_ring [hRA, hAR]

theorem factor_residual_to_cayley_recurrence_raw {n : ℕ}
    (alpha k : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (uNow uNext residual : Fin n → ℂ)
    (hfactor :
      (cayleyA alpha H).mulVec uNext =
        (cayleyB alpha H).mulVec uNow + k • residual) :
    uNext =
      (cayleyU alpha H (cayleyR alpha H)).mulVec uNow +
        (cayleyR alpha H).mulVec (k • residual) := by
  have h := congrArg (fun v => (cayleyR alpha H).mulVec v) hfactor
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    cayleyR_mul_cayleyA alpha H hH,
    cayleyR_mul_cayleyB_eq_cayleyU alpha H hH,
    Matrix.one_mulVec] at h
  exact h

theorem factor_residual_to_cayley_recurrence_euclidean {n : ℕ}
    (alpha k : ℝ) (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (uNow uNext residual : VecState n)
    (hfactor :
      euclideanAction (cayleyA alpha H) uNext =
        euclideanAction (cayleyB alpha H) uNow + k • residual) :
    uNext =
      euclideanAction (cayleyU alpha H (cayleyR alpha H)) uNow +
        euclideanAction (cayleyR alpha H) (k • residual) := by
  ext i
  have hf :
      (cayleyA alpha H).mulVec (WithLp.ofLp uNext) =
        (cayleyB alpha H).mulVec (WithLp.ofLp uNow) +
          k • WithLp.ofLp residual := by
    simpa [euclideanAction] using congrArg WithLp.ofLp hfactor
  have hr := factor_residual_to_cayley_recurrence_raw alpha k H hH
    (WithLp.ofLp uNow) (WithLp.ofLp uNext) (WithLp.ofLp residual) hf
  exact congrFun hr i

def recurrenceIdentityStatus : String :=
  "factor_residual_exactly_converted_to_cayley_recurrence_with_inverse_defect"

end NDEAMathlibGate.CayleyResidualRecurrenceIdentityV1
