import InfiniteClosure
import CutoffSchedule

/-! Non-vacuous convergence to the full Fourier evolution at terminal time one. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp009

theorem scheduled_infinite_grid_error (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) (ha : Summable fun m => ‖a m‖) :
    infiniteGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial ≤
      infiniteInitialError (gridIndex q) (mesh q) a initial + Real.sqrt (2*Real.pi)*
        ((Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)*mass a +
          2*tail (cutoff q) a) := by
  simpa only [one_mul] using infinite_grid_error_bound (cutoff q) (gridIndex q)
    (mesh q) (timeStep q) 1 (stepCount q) a initial ha (cutoff_pos q)
    (cutoff_unaliased q) (mesh_period q) (mesh_pos q) (cutoff_mesh_le_one q)
    (timeStep_nonneg q) (timeStep_restriction q) (stepCount_timeStep q).le

theorem scheduled_infinite_error_tendsto_zero (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖)
    (initial : (q : ℕ) → Vec (Grid (gridIndex q)))
    (hi : Filter.Tendsto (fun q => infiniteInitialError (gridIndex q) (mesh q) a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => infiniteGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (initial q)) Filter.atTop (nhds 0) :=
  infinite_mesh_error_tendsto_zero a ha cutoff gridIndex stepCount mesh timeStep 1 initial
    cutoff_pos cutoff_unaliased mesh_period mesh_pos cutoff_mesh_le_one timeStep_nonneg
    timeStep_restriction (fun q => (stepCount_timeStep q).le) cutoff_tendsto_atTop
    cutoff_error_tendsto_zero hi

theorem scheduled_exact_initial_error_tendsto_zero (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    Filter.Tendsto (fun q => infiniteGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (infiniteGrid (gridIndex q) (mesh q) a 0))
      Filter.atTop (nhds 0) := by
  apply scheduled_infinite_error_tendsto_zero a ha
  simpa only [infinite_exact_initial_error] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds 0))

theorem scheduled_reference_time_one (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) :
    infiniteGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial =
      Real.sqrt (mesh q)*‖(symmetric (gridIndex q) (mesh q) (timeStep q)
        Exp007.Z Exp007.X ^ stepCount q) initial - infiniteGrid (gridIndex q) (mesh q) a 1‖ := by
  unfold infiniteGridError
  rw [stepCount_timeStep]

end NDEAEvolve.Exp009
