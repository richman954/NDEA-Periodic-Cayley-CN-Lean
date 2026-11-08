import UniformGridTimeConvergence

/-! Explicit original-data claims and endpoint-inclusion controls.
These do not extend the mathematical assumptions or prove a convergence rate. -/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
namespace NDEAEvolve.Exp016.Verification

theorem time_one_spec
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => Exp015.spatialL2 (fun x =>
      fourierReconstruction (initialSamplingCutoff q) (initialSamplingMesh q)
        (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q) v
          (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
          (fun _ => temporalStepSize q) (temporalStepCount q)) x -
      Exp014.solution v a 1 x) b (2 * Real.pi)) atTop (𝓝 0) := by
  exact scheduledCayley_baseline_timeOne_error_tendsto_zero v hv hHerm a b

theorem finite_horizon_spec (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q =>
      (Finset.range (temporalStepCount q + 1)).sup' ⟨0, by simp⟩ (fun N =>
        Exp015.spatialL2 (fun x =>
          fourierReconstruction (initialSamplingCutoff q) (initialSamplingMesh q)
            (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q) v
              (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
              (fun _ => horizonStepSize T q) N) x -
          Exp014.solution v a ((N : ℝ) * horizonStepSize T q) x)
          b (2 * Real.pi))) atTop (𝓝 0) := by
  refine Filter.Tendsto.congr ?_ (horizonGridError_tendsto_zero T hT v hv hHerm a b)
  intro q
  simpa only [sampledCayleySolutionError] using
    horizonGridError_eq_max_at_nk v a b T q

theorem initial_error_in_max (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) :
    sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
      (fun _ => horizonStepSize T q) 0 b
      (actualCayleyTime (fun _ => horizonStepSize T q) 0) ≤ horizonGridError v a b T q := by
  exact (horizonGridError_le_iff v a b T q _).mp le_rfl 0 (Nat.zero_le _)

theorem endpoint_error_in_max (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) :
    sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
      (fun _ => horizonStepSize T q) (temporalStepCount q) b
      (actualCayleyTime (fun _ => horizonStepSize T q) (temporalStepCount q)) ≤
      horizonGridError v a b T q := by
  exact (horizonGridError_le_iff v a b T q _).mp le_rfl _ le_rfl
end NDEAEvolve.Exp016.Verification
