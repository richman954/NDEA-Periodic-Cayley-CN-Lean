import NDEAMathlibGate.CayleyFactorResidualGlobalErrorV1
import NDEAMathlibGate.PeriodicRotatedCayleyScaledDefectV1

/-! Concrete fixed-time convergence facade for the periodic Cayley/CN scheme. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicCayleyCrankNicolsonConvergenceV1

open NDEAMathlibGate.CayleyEuclideanIsometryV1
open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR
open NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1
open NDEAMathlibGate.CayleyFactorResidualGlobalErrorV1
open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicRotatedSpaceTimeVectorConsistencyV1
open NDEAMathlibGate.PeriodicRotatedCayleyScaledDefectV1
open NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1
open NDEAMathlibGate.WeightedCayleyGlobalErrorV1

abbrev periodicH (L : ℝ) (m : ℕ) :=
  NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
    (meshWidth L (m + 1)) (m + 1)

def sampledExactState
    (L : ℝ) (m : ℕ) (profile : ℕ → ℝ → ℂ) (j : ℕ) : VecState (m + 1) :=
  WithLp.toLp 2 (sampleFixedPeriod L (m + 1) (profile j))

def sampledCNTemporalResidual
    (L k : ℝ) (m : ℕ) (profile : ℕ → ℝ → ℂ)
    (timeDerivative : ℕ → Fin (m + 1) → ℂ) (j : ℕ) : Fin (m + 1) → ℂ :=
  NDEAMathlibGate.CayleySampledPDEFactorIdentityV1.cnResidualVector
    (sampleFixedPeriod L (m + 1) (profile j))
    (sampleFixedPeriod L (m + 1) (profile (j + 1)))
    (timeDerivative j) (timeDerivative (j + 1)) k

def sampledRotatedResidual
    (L k : ℝ) (m : ℕ) (profile : ℕ → ℝ → ℂ)
    (timeDerivative : ℕ → Fin (m + 1) → ℂ) (j : ℕ) : VecState (m + 1) :=
  rotatedSpaceTimeResidualEuclidean m
    (sampledCNTemporalResidual L k m profile timeDerivative j) L
    (averageProfile (profile j) (profile (j + 1)))

theorem periodic_cayley_cn_fixed_time_error
    (L : ℝ) (hL : 0 < L) (m : ℕ)
    (k T Mt Ms : ℝ) (hk : 0 < k) (hMt : 0 ≤ Mt)
    (sampledExact numerical residual : ℕ → VecState (m + 1))
    (spatialProfile : ℕ → ℝ → ℂ)
    (temporalResidual : ℕ → Fin (m + 1) → ℂ)
    (hPeriodic : ∀ j, Function.Periodic (spatialProfile j) L)
    (hSpatialC4 : ∀ j, ContDiff ℝ 4 (spatialProfile j))
    (hSpatialDeriv : ∀ j x, ‖iteratedDeriv 4 (spatialProfile j) x‖ ≤ Ms)
    (hTemporal : ∀ j i,
      ‖temporalResidual j i‖ ≤ 5 * Mt * k ^ 2 / 12)
    (hresidual : ∀ j,
      residual j = rotatedSpaceTimeResidualEuclidean
        m (temporalResidual j) L (spatialProfile j))
    (hfactor : ∀ j,
      euclideanAction (cayleyA (k / 2) (periodicH L m))
          (sampledExact (j + 1)) =
        euclideanAction (cayleyB (k / 2) (periodicH L m))
            (sampledExact j) + k • residual j)
    (hnumerical : ∀ j, numerical (j + 1) =
      euclideanAction
        (cayleyU (k / 2) (periodicH L m) (cayleyR (k / 2) (periodicH L m)))
        (numerical j))
    (N : ℕ) (horizon : (N : ℝ) * k ≤ T) :
    weightedNorm (meshWidth L (m + 1))
        (sampledExact N - numerical N) ≤
      weightedNorm (meshWidth L (m + 1))
          (sampledExact 0 - numerical 0) +
        T * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
          (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2) := by
  have hH : IsHermitian (periodicH L m) :=
    NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian_isHermitian
      (meshWidth L (m + 1)) (m + 1)
  have hMs : 0 ≤ Ms := (norm_nonneg _).trans (hSpatialDeriv 0 0)
  have hCt : 0 ≤ Real.sqrt L * (5 * Mt / 12) := by positivity
  have hCs : 0 ≤ Real.sqrt L * (Ms / 12) := by positivity
  apply factor_residual_fixed_time_weighted_error
    (meshWidth L (m + 1)) (k / 2) k (meshWidth L (m + 1)) T
      (Real.sqrt L * (5 * Mt / 12)) (Real.sqrt L * (Ms / 12))
      (periodicH L m) hH sampledExact numerical residual hfactor hnumerical
      N hCt hCs horizon
  intro j
  rw [hresidual j]
  simpa [NDEAMathlibGate.PeriodicCayleyScaledDefectV1.scaledDefect] using
    periodic_rotated_scaled_defect_weightedNorm_bound
      L hL (spatialProfile j) (hPeriodic j) (hSpatialC4 j) Ms
        (hSpatialDeriv j) m (temporalResidual j) k Mt hk.le hMt (hTemporal j)

theorem periodic_cayley_cn_sampled_trajectory_fixed_time_error
    (L : ℝ) (hL : 0 < L) (m : ℕ)
    (k T Mt Ms : ℝ) (hk : 0 < k) (hMt : 0 ≤ Mt)
    (profile : ℕ → ℝ → ℂ)
    (timeDerivative : ℕ → Fin (m + 1) → ℂ)
    (numerical : ℕ → VecState (m + 1))
    (hPDEAverage : ∀ j,
      (2 : ℂ)⁻¹ • (timeDerivative (j + 1) + timeDerivative j) =
        Complex.I • sampledSecondDerivative L (m + 1)
          (averageProfile (profile j) (profile (j + 1))))
    (hPeriodic : ∀ j,
      Function.Periodic (averageProfile (profile j) (profile (j + 1))) L)
    (hSpatialC4 : ∀ j,
      ContDiff ℝ 4 (averageProfile (profile j) (profile (j + 1))))
    (hSpatialDeriv : ∀ j x,
      ‖iteratedDeriv 4 (averageProfile (profile j) (profile (j + 1))) x‖ ≤ Ms)
    (hTemporal : ∀ j i,
      ‖sampledCNTemporalResidual L k m profile timeDerivative j i‖ ≤
        5 * Mt * k ^ 2 / 12)
    (hnumerical : ∀ j, numerical (j + 1) =
      euclideanAction
        (cayleyU (k / 2) (periodicH L m) (cayleyR (k / 2) (periodicH L m)))
        (numerical j))
    (N : ℕ) (horizon : (N : ℝ) * k ≤ T) :
    weightedNorm (meshWidth L (m + 1))
        (sampledExactState L m profile N - numerical N) ≤
      weightedNorm (meshWidth L (m + 1))
          (sampledExactState L m profile 0 - numerical 0) +
        T * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
          (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2) := by
  apply periodic_cayley_cn_fixed_time_error L hL m k T Mt Ms hk hMt
    (sampledExactState L m profile) numerical
    (sampledRotatedResidual L k m profile timeDerivative)
    (fun j => averageProfile (profile j) (profile (j + 1)))
    (sampledCNTemporalResidual L k m profile timeDerivative)
    hPeriodic hSpatialC4 hSpatialDeriv hTemporal
  · intro j
    rfl
  · intro j
    exact periodic_sampled_factor_equation_euclidean L k hk.ne' m
      (profile j) (profile (j + 1))
      (timeDerivative j) (timeDerivative (j + 1)) (hPDEAverage j)
  · exact hnumerical
  · exact horizon

def periodicCayleyCNConvergenceStatus : String :=
  "periodic_cayley_crank_nicolson_fixed_time_Ok2_plus_Oh2_validated"

end NDEAMathlibGate.PeriodicCayleyCrankNicolsonConvergenceV1
