import NDEAMathlibGate.CayleyEuclideanIsometryV1
import NDEAMathlibGate.PeriodicSpaceTimeVectorConsistencyV1

/-! Stable accumulation and fixed-time error for Cayley action in weighted L2. -/

noncomputable section

open scoped BigOperators

namespace NDEAMathlibGate.WeightedCayleyGlobalErrorV1

open NDEAMathlibGate.CayleyEuclideanIsometryV1

abbrev weightedNorm {n : ℕ} (h : ℝ) (psi : VecState n) : ℝ :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm h psi

theorem weightedNorm_add_le {n : ℕ} (h : ℝ) (x y : VecState n) :
    weightedNorm h (x + y) ≤ weightedNorm h x + weightedNorm h y := by
  unfold weightedNorm NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
  calc
    Real.sqrt h * ‖x + y‖ ≤ Real.sqrt h * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le x y) (Real.sqrt_nonneg h)
    _ = Real.sqrt h * ‖x‖ + Real.sqrt h * ‖y‖ := by ring

theorem cayley_weighted_distance_preserved {n : ℕ}
    (weight alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (x y : VecState n) :
    weightedNorm weight
        (euclideanAction
            (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
              (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H)) x -
          euclideanAction
            (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
              (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H)) y) =
      weightedNorm weight (x - y) := by
  unfold weightedNorm NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
  rw [cayley_euclideanAction_isometry_without_external_inverse alpha H hH]

theorem cayley_weighted_error_accumulation {n : ℕ}
    (weight alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (approx exact defect : ℕ → VecState n)
    (happrox : ∀ j : ℕ, approx (j + 1) =
      euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H))
        (approx j) + defect j)
    (hexact : ∀ j : ℕ, exact (j + 1) =
      euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H))
        (exact j)) (N : ℕ) :
    weightedNorm weight (approx N - exact N) ≤
      weightedNorm weight (approx 0 - exact 0) +
        ∑ j ∈ Finset.range N, weightedNorm weight (defect j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [happrox N, hexact N]
      calc
        weightedNorm weight
            (euclideanAction _ (approx N) + defect N -
              euclideanAction _ (exact N)) =
            weightedNorm weight
              ((euclideanAction _ (approx N) - euclideanAction _ (exact N)) +
                defect N) := by
          congr 2
          abel
        _ ≤ weightedNorm weight
              (euclideanAction _ (approx N) - euclideanAction _ (exact N)) +
            weightedNorm weight (defect N) := weightedNorm_add_le _ _ _
        _ = weightedNorm weight (approx N - exact N) +
            weightedNorm weight (defect N) := by
          rw [cayley_weighted_distance_preserved weight alpha H hH]
        _ ≤ (weightedNorm weight (approx 0 - exact 0) +
              ∑ j ∈ Finset.range N, weightedNorm weight (defect j)) +
            weightedNorm weight (defect N) := add_le_add ih (le_refl _)
        _ = weightedNorm weight (approx 0 - exact 0) +
              ∑ j ∈ Finset.range (N + 1), weightedNorm weight (defect j) := by
          rw [Finset.sum_range_succ]
          ring

theorem cayley_weighted_fixed_time_error {n : ℕ}
    (weight alpha : ℝ) (H : Mat n)
    (hH : NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian H)
    (approx exact defect : ℕ → VecState n)
    (happrox : ∀ j : ℕ, approx (j + 1) =
      euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H))
        (approx j) + defect j)
    (hexact : ∀ j : ℕ, exact (j + 1) =
      euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU alpha H
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR alpha H))
        (exact j))
    (k h T Ct Cs : ℝ) (N : ℕ) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hdefect : ∀ j, weightedNorm weight (defect j) ≤
      k * (Ct * k ^ 2 + Cs * h ^ 2)) :
    weightedNorm weight (approx N - exact N) ≤
      weightedNorm weight (approx 0 - exact 0) +
        T * (Ct * k ^ 2 + Cs * h ^ 2) := by
  have hrate : 0 ≤ Ct * k ^ 2 + Cs * h ^ 2 :=
    add_nonneg (mul_nonneg hCt (sq_nonneg k))
      (mul_nonneg hCs (sq_nonneg h))
  calc
    weightedNorm weight (approx N - exact N) ≤
        weightedNorm weight (approx 0 - exact 0) +
          ∑ j ∈ Finset.range N, weightedNorm weight (defect j) :=
      cayley_weighted_error_accumulation weight alpha H hH
        approx exact defect happrox hexact N
    _ ≤ weightedNorm weight (approx 0 - exact 0) +
          ∑ _j ∈ Finset.range N, k * (Ct * k ^ 2 + Cs * h ^ 2) := by
      gcongr with j hj
      exact hdefect j
    _ = weightedNorm weight (approx 0 - exact 0) +
          (N : ℝ) * (k * (Ct * k ^ 2 + Cs * h ^ 2)) := by simp
    _ ≤ weightedNorm weight (approx 0 - exact 0) +
          T * (Ct * k ^ 2 + Cs * h ^ 2) := by
      apply add_le_add (le_refl _)
      calc
        (N : ℝ) * (k * (Ct * k ^ 2 + Cs * h ^ 2)) =
            ((N : ℝ) * k) * (Ct * k ^ 2 + Cs * h ^ 2) := by ring
        _ ≤ T * (Ct * k ^ 2 + Cs * h ^ 2) :=
          mul_le_mul_of_nonneg_right horizon hrate

def weightedCayleyGlobalStatus : String :=
  "weighted_L2_cayley_fixed_time_error_accumulation_validated"

end NDEAMathlibGate.WeightedCayleyGlobalErrorV1
