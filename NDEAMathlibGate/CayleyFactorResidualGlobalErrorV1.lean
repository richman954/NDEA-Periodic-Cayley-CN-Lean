import NDEAMathlibGate.CayleyInverseContractionV1
import NDEAMathlibGate.CayleyResidualRecurrenceIdentityV1
import NDEAMathlibGate.WeightedCayleyGlobalErrorV1

/-!
Turn a per-step Cayley factor residual into a fixed-time weighted error bound.
-/

noncomputable section

namespace NDEAMathlibGate.CayleyFactorResidualGlobalErrorV1

open NDEAMathlibGate.CayleyEuclideanIsometryV1
open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR
open NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1
open NDEAMathlibGate.CayleyResidualRecurrenceIdentityV1
open NDEAMathlibGate.WeightedCayleyGlobalErrorV1

theorem factor_residual_fixed_time_weighted_error {n : ℕ}
    (weight alpha k h T Ct Cs : ℝ)
    (H : CayleyEuclideanIsometryV1.Mat n)
    (hH : IsHermitian H)
    (sampledExact numerical residual : ℕ → VecState n)
    (hfactor : ∀ j : ℕ,
      euclideanAction (cayleyA alpha H) (sampledExact (j + 1)) =
        euclideanAction (cayleyB alpha H) (sampledExact j) +
          k • residual j)
    (hnumerical : ∀ j : ℕ, numerical (j + 1) =
      euclideanAction (cayleyU alpha H (cayleyR alpha H)) (numerical j))
    (N : ℕ) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hscaled : ∀ j : ℕ,
      weightedNorm weight (k • residual j) ≤
        k * (Ct * k ^ 2 + Cs * h ^ 2)) :
    weightedNorm weight (sampledExact N - numerical N) ≤
      weightedNorm weight (sampledExact 0 - numerical 0) +
        T * (Ct * k ^ 2 + Cs * h ^ 2) := by
  let defect : ℕ → VecState n := fun j =>
    euclideanAction (cayleyR alpha H) (k • residual j)
  have hsampled : ∀ j : ℕ, sampledExact (j + 1) =
      euclideanAction (cayleyU alpha H (cayleyR alpha H)) (sampledExact j) +
        defect j := by
    intro j
    exact factor_residual_to_cayley_recurrence_euclidean
      alpha k H hH (sampledExact j) (sampledExact (j + 1))
        (residual j) (hfactor j)
  have hdefect : ∀ j : ℕ, weightedNorm weight (defect j) ≤
      k * (Ct * k ^ 2 + Cs * h ^ 2) := by
    intro j
    calc
      weightedNorm weight (defect j) ≤
          weightedNorm weight (k • residual j) :=
        NDEAMathlibGate.CayleyInverseContractionV1.cayleyR_weightedNorm_le
          weight alpha H hH (k • residual j)
      _ ≤ k * (Ct * k ^ 2 + Cs * h ^ 2) := hscaled j
  exact cayley_weighted_fixed_time_error weight alpha H hH
    sampledExact numerical defect hsampled hnumerical k h T Ct Cs N
      hCt hCs horizon hdefect

def factorResidualGlobalErrorStatus : String :=
  "factor_residual_to_fixed_time_weighted_second_order_error_validated"

end NDEAMathlibGate.CayleyFactorResidualGlobalErrorV1
