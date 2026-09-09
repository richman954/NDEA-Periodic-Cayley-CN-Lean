import StageBridge

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
namespace NDEAEvolve.Exp007.Controls
open SpinorGrid

def initialSpinor : E 2 := WithLp.toLp 2 ![(1 : ℂ), 0]

theorem initialSpinor_norm : ‖initialSpinor‖ = 1 := by
  have hs : ‖initialSpinor‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [initialSpinor, Fin.sum_univ_two]
  nlinarith [norm_nonneg initialSpinor]

theorem admissible_eight_point_grid :
    (0 : ℝ) < Real.pi/4 ∧ Real.pi/4 ≤ 1 ∧
    ((7+1 : ℕ) : ℝ)*(Real.pi/4) = 2*Real.pi ∧
    (0 : ℝ) < 1/12 ∧ (1/12 : ℝ) ≤ 1/6 := by
  refine ⟨by positivity, ?_, ?_, by norm_num, by norm_num⟩
  · linarith [Real.pi_le_four]
  · norm_num <;> ring

theorem coupling_is_active : (operatorOf X initialSpinor) 1 = 1 := by
  norm_num [operatorOf, initialSpinor, X, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem initial_solution_is_spatially_nonconstant :
    U initialSpinor 0 0 ≠ U initialSpinor 0 Real.pi := by
  intro h
  have hc := congrArg (fun w : E 2 => w 0) h
  norm_num [U, v_initial, Exp006.phase, initialSpinor, Complex.exp_pi_mul_I] at hc

theorem omitted_coupling_commutes (lambda : ℝ) : Commute (A lambda) (0 : Mat 2) := by
  exact Commute.zero_right _

theorem zero_mesh_consistency_fails :
    ¬ |Exp006.spatialSymbol 0-1| ≤ (0 : ℝ)^2/8 := by
  norm_num [Exp006.spatialSymbol]

theorem empty_trajectory_retains_initial_error (n : ℕ) (h k : ℝ)
    (initial : Vec (Grid n)) (v0 : E 2) :
    gridError n h k 0 initial v0 = initialError n h initial v0 := by
  simp [gridError, initialError]

#print axioms initialSpinor_norm
#print axioms admissible_eight_point_grid
#print axioms coupling_is_active
#print axioms initial_solution_is_spatially_nonconstant
#print axioms omitted_coupling_commutes
#print axioms zero_mesh_consistency_fails
#print axioms empty_trajectory_retains_initial_error
end NDEAEvolve.Exp007.Controls
