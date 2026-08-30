import NDEAMathlibGate.SampledSharpSpatialConsistencyV1

/-! Production V1: uniform finite-vector sup-norm consistency. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEAUniformVectorSpatialConsistencyProbe

open NDEAPeriodicSamplingBridgeProbe
open NDEASampledSharpSpatialConsistencyProbe

def sampledResidualVector
    (L : ℝ) (u : ℝ → ℂ) (m : ℕ) : Fin (m + 1) → ℂ :=
  fun i ↦
    (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
      (meshWidth L (m + 1)) (m + 1)).mulVec
        (sampleFixedPeriod L (m + 1) u) i +
      iteratedDeriv 2 u (gridPoint L (m + 1) i)

@[simp] theorem sampledResidualVector_apply
    (L : ℝ) (u : ℝ → ℂ) (m : ℕ) (i : Fin (m + 1)) :
    sampledResidualVector L u m i =
      (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
        (meshWidth L (m + 1)) (m + 1)).mulVec
          (sampleFixedPeriod L (m + 1) u) i +
        iteratedDeriv 2 u (gridPoint L (m + 1) i) := by
  rfl

theorem sampledResidualVector_supNorm_sharp
    (L : ℝ) (hL : 0 < L)
    (u : ℝ → ℂ)
    (huPeriodic : Function.Periodic u L)
    (huC4 : ContDiff ℝ 4 u)
    (M : ℝ)
    (hderiv : ∀ t : ℝ, ‖iteratedDeriv 4 u t‖ ≤ M)
    (m : ℕ) :
    ‖sampledResidualVector L u m‖ ≤
      M * (meshWidth L (m + 1)) ^ 2 / 12 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hderiv 0)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  exact sampled_periodic_negLaplacian_spatial_consistency_sharp
    L hL u huPeriodic huC4 M hderiv i

#check sampledResidualVector_supNorm_sharp
#print axioms sampledResidualVector_supNorm_sharp

end NDEAUniformVectorSpatialConsistencyProbe
