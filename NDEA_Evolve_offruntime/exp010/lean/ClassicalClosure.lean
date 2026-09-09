import Continuity
import WeightedClosure
import ScheduleClosure

/-! Actual numerical errors against pointwise samples of the classical PDE solution. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp010

def sampleSolution (n : ℕ) (h : ℝ) (u : ℝ → ℝ → E 2) (t : ℝ) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => u t ((p.1.val:ℝ)*h) p.2)

def classicalGridError (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial -
    sampleSolution n h (infiniteSolution a) ((N:ℝ)*k)‖

def classicalInitialError (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial - sampleSolution n h (infiniteSolution a) 0‖

theorem sampleSolution_eq_infiniteGrid (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Regular a) (t : ℝ) :
    sampleSolution n h (infiniteSolution a) t = infiniteGrid n h a t := by
  ext p
  exact (infiniteGrid_is_sampled_solution n h a (regular_absolute a ha) t p).symm

theorem classicalGridError_eq (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (ha : Regular a) (initial : Vec (Grid n)) :
    classicalGridError n h k N a initial = infiniteGridError n h k N a initial := by
  unfold classicalGridError infiniteGridError
  rw [sampleSolution_eq_infiniteGrid n h a ha]

theorem classicalInitialError_eq (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Regular a) (initial : Vec (Grid n)) :
    classicalInitialError n h a initial = infiniteInitialError n h a initial := by
  unfold classicalInitialError infiniteInitialError
  rw [sampleSolution_eq_infiniteGrid n h a ha]

theorem classical_grid_error_bound (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) (ha : Regular a)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    classicalGridError n h k N a initial ≤ classicalInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a +
        2*(moment 2 a / ((M:ℝ)+1)^2)) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  rw [classicalGridError_eq n h k N a ha, classicalInitialError_eq n h a ha]
  exact weighted_infinite_grid_error_bound 2 M n h k T N a initial ha
    hM hband hmesh hh hMh hk hstep horizon

theorem scheduled_classical_reference_time_one (q : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid (gridIndex q))) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) (stepCount q) a initial =
      Real.sqrt (mesh q)*‖(symmetric (gridIndex q) (mesh q) (timeStep q)
        Exp007.Z Exp007.X ^ stepCount q) initial -
          sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 1‖ := by
  unfold classicalGridError
  rw [stepCount_timeStep]

theorem scheduled_classical_error_tendsto_zero (a : ℤ → E 2) (ha : Regular a)
    (initial : (q : ℕ) → Vec (Grid (gridIndex q)))
    (hi : Filter.Tendsto (fun q => classicalInitialError (gridIndex q) (mesh q) a (initial q))
      Filter.atTop (nhds 0)) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    Filter.Tendsto (fun q => classicalGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (initial q)) Filter.atTop (nhds 0) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  simp only [classicalInitialError_eq _ _ a ha] at hi
  simp only [classicalGridError_eq _ _ _ _ a ha]
  exact scheduled_infinite_error_tendsto_zero a (regular_absolute a ha) initial hi

theorem scheduled_classical_exact_initial_convergence (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    Filter.Tendsto (fun q => classicalGridError (gridIndex q) (mesh q) (timeStep q)
      (stepCount q) a (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0))
      Filter.atTop (nhds 0) := by
  refine ⟨infiniteSolution_classical a ha, ?_⟩
  simp only [classicalGridError_eq _ _ _ _ a ha, sampleSolution_eq_infiniteGrid _ _ a ha]
  exact scheduled_exact_initial_error_tendsto_zero a (regular_absolute a ha)

end NDEAEvolve.Exp010
