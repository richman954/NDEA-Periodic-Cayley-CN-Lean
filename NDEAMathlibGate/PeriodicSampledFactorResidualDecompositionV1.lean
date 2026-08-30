import NDEAMathlibGate.CayleySampledPDEFactorIdentityV1
import NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1

/-! Identify the Cayley spatial mismatch with the periodic sampled residual. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1

open Complex
open NDEAMathlibGate.CayleySampledPDEFactorIdentityV1
open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1

def averageProfile (uNow uNext : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (uNext x + uNow x) / 2

def sampledSecondDerivative
    (L : ℝ) (n : ℕ) (u : ℝ → ℂ) : Fin n → ℂ :=
  fun i => iteratedDeriv 2 u (gridPoint L n i)

theorem sample_average_profile
    (L : ℝ) (n : ℕ) (uNow uNext : ℝ → ℂ) :
    sampleFixedPeriod L n (averageProfile uNow uNext) =
      (2 : ℂ)⁻¹ •
        (sampleFixedPeriod L n uNext + sampleFixedPeriod L n uNow) := by
  ext i
  simp [averageProfile, sampleFixedPeriod]
  ring

theorem periodic_spatialMismatch_eq_sampledResidual
    (L : ℝ) (m : ℕ) (uNow uNext : ℝ → ℂ) :
    spatialMismatchVector
        (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
          (meshWidth L (m + 1)) (m + 1))
        (sampleFixedPeriod L (m + 1) uNow)
        (sampleFixedPeriod L (m + 1) uNext)
        (sampledSecondDerivative L (m + 1) (averageProfile uNow uNext)) =
      sampledResidualVector L (averageProfile uNow uNext) m := by
  unfold spatialMismatchVector sampledSecondDerivative
  rw [← sample_average_profile L (m + 1) uNow uNext]
  rfl

theorem periodic_sampled_factor_equation_raw
    (L k : ℝ) (hk : k ≠ 0) (m : ℕ)
    (uNowProfile uNextProfile : ℝ → ℂ)
    (duNow duNext : Fin (m + 1) → ℂ)
    (hPDEAverage : (2 : ℂ)⁻¹ • (duNext + duNow) =
      Complex.I • sampledSecondDerivative L (m + 1)
        (averageProfile uNowProfile uNextProfile)) :
    (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyA (k / 2)
        (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
          (meshWidth L (m + 1)) (m + 1))).mulVec
          (sampleFixedPeriod L (m + 1) uNextProfile) =
      (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyB (k / 2)
        (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
          (meshWidth L (m + 1)) (m + 1))).mulVec
          (sampleFixedPeriod L (m + 1) uNowProfile) +
        k • (fun i =>
          cnResidualVector
              (sampleFixedPeriod L (m + 1) uNowProfile)
              (sampleFixedPeriod L (m + 1) uNextProfile)
              duNow duNext k i +
            Complex.I *
              sampledResidualVector L
                (averageProfile uNowProfile uNextProfile) m i) := by
  let H := NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
    (meshWidth L (m + 1)) (m + 1)
  have hfactor := general_derivative_to_factor_residual k hk H
    (sampleFixedPeriod L (m + 1) uNowProfile)
    (sampleFixedPeriod L (m + 1) uNextProfile) duNow duNext
  have hdecomp := combined_factor_residual_eq_rotated_space_time H
    (sampleFixedPeriod L (m + 1) uNowProfile)
    (sampleFixedPeriod L (m + 1) uNextProfile) duNow duNext
    (sampledSecondDerivative L (m + 1)
      (averageProfile uNowProfile uNextProfile)) k hPDEAverage
  rw [hdecomp] at hfactor
  unfold rotatedSpaceTimeResidualVector at hfactor
  dsimp [H] at hfactor
  rw [periodic_spatialMismatch_eq_sampledResidual
    L m uNowProfile uNextProfile] at hfactor
  ext i
  have hi := congrFun hfactor i
  simpa [Pi.add_apply, Pi.smul_apply] using hi

def periodicSampledFactorDecompositionStatus : String :=
  "factor_spatial_mismatch_identified_with_periodic_average_profile_residual"

end NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1
