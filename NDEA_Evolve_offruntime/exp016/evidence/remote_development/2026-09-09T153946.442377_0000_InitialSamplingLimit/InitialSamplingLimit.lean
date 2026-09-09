import InitialSamplingBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! Convergence of the actual sampled initial-field reconstruction.
This concerns initialization only. No time-stepping or solver limit is asserted.
-/
noncomputable section
open Filter
open scoped Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
namespace NDEAEvolve.Exp016

/-- The actual initialization error vanishes along any expanding full odd grid. -/
theorem sampledInitialState_spatialL2_tendsto_zero
    (M : ℕ → ℕ) (h : ℕ → ℝ)
    (hmesh : ∀ j, ((2 * M j + 1 : ℕ) : ℝ) * h j = 2 * Real.pi)
    (hM : Tendsto M atTop atTop) (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun j => Exp015.spatialL2
      (fun x => fourierReconstruction (M j) (h j)
        (sampledInitialState (M j) (h j) a) x - Exp014.synth a x)
      b (2 * Real.pi)) atTop (𝓝 0) := by
  have hi : Tendsto (fun j => (1 + (M j : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_comm] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        ((tendsto_add_atTop_nat 1).comp hM)
  have hmajor : Tendsto
      (fun j => 2 * Real.sqrt (2 * Real.pi) * (‖a‖ / (1 + (M j : ℝ)) ^ 2))
      atTop (𝓝 0) := by
    have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
    simpa only [div_eq_mul_inv, inv_pow, hzero, mul_zero] using
      ((hi.pow 2).const_mul ‖a‖).const_mul (2 * Real.sqrt (2 * Real.pi))
  exact squeeze_zero (fun j => Exp015.spatialL2_nonneg _ _ _)
    (fun j => sampledInitialState_spatialL2_le_weighted (M j) (h j) (hmesh j) a b)
    hmajor

def initialSamplingCutoff (j : ℕ) : ℕ := j + 1

def initialSamplingMesh (j : ℕ) : ℝ :=
  2 * Real.pi / ((2 * initialSamplingCutoff j + 1 : ℕ) : ℝ)

/-- Explicit initialization convergence for M_j = j+1 and h_j = 2π/(2M_j+1). -/
theorem scheduledInitialSampling_spatialL2_tendsto_zero
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun j => Exp015.spatialL2
      (fun x => fourierReconstruction (initialSamplingCutoff j) (initialSamplingMesh j)
        (sampledInitialState (initialSamplingCutoff j) (initialSamplingMesh j) a) x -
        Exp014.synth a x) b (2 * Real.pi)) atTop (𝓝 0) := by
  apply sampledInitialState_spatialL2_tendsto_zero initialSamplingCutoff initialSamplingMesh
  · intro j
    unfold initialSamplingMesh
    have hn : (((2 * initialSamplingCutoff j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    exact mul_div_cancel₀ (2 * Real.pi) hn
  · exact tendsto_add_atTop_nat 1

#print axioms sampledInitialState_spatialL2_tendsto_zero
#print axioms scheduledInitialSampling_spatialL2_tendsto_zero
end NDEAEvolve.Exp016
