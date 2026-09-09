import Exp005ModeBridge

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp006.Controls

/-- A concrete admissible grid/time witness; the production hypotheses are satisfiable. -/
theorem admissible_eight_point_grid :
    (0 : ℝ) < Real.pi/4 ∧ Real.pi/4 ≤ 1 ∧
    ((7+1 : ℕ) : ℝ)*(Real.pi/4) = 2*Real.pi ∧
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 2 := by
  constructor
  · positivity
  constructor
  · linarith [Real.pi_le_four]
  constructor
  · norm_num <;> ring
  norm_num

/-- The excluded zero mesh falsifies the spatial consistency statement. -/
theorem zero_mesh_consistency_false :
    ¬ |spatialSymbol 0 - 1| ≤ (0 : ℝ)^2/8 := by
  norm_num [spatialSymbol]

/-- The discrete first mode has a strictly nonzero spatial defect. -/
theorem spatial_error_is_present (h : ℝ) (hh : 0 < h) : spatialSymbol h ≠ 1 :=
  ne_of_lt (spatialSymbol_strictly_below_continuum h hh.ne')

/-- The first Fourier mode is not the constant zero solution. -/
theorem solution_nonconstant_and_nonzero (t : ℝ) :
    (∃ x y, mode t x ≠ mode t y) ∧ (∀ x, mode t x ≠ 0) :=
  ⟨mode_nonconstant t, mode_nonzero t⟩

/-- Both equal split Laplacians act nontrivially on this solution. -/
theorem both_continuous_generators_active (t x : ℝ) :
    -deriv (deriv (mode t)) x = mode t x ∧
    -deriv (deriv (mode t)) x ≠ 0 := by
  have hsecond : deriv (deriv (mode t)) x = - mode t x := by
    simpa using! mode_second_derivative t x
  rw [hsecond]
  simpa using mode_nonzero t x

/-- Exact zero time-step control on the measured scalar factors. -/
theorem zero_step_residual (h x : ℝ) : scalarFactorResidual h 0 x = 0 := by
  simp [scalarFactorResidual]

#print axioms admissible_eight_point_grid
#print axioms zero_mesh_consistency_false
#print axioms spatial_error_is_present
#print axioms solution_nonconstant_and_nonzero
#print axioms both_continuous_generators_active
#print axioms zero_step_residual
end NDEAEvolve.Exp006.Controls
