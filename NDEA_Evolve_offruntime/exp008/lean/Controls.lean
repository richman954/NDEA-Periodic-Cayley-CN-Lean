import SuperpositionClosure

/-! Concrete controls for signed superpositions, aliasing, initial error,
and frequency-dependent constants. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008.Controls
open FourierGrid

def activeSpectrum : Finset ℤ := {-1, 0, 1}

def activeCoefficients (m : ℤ) : E 2 :=
  (if m = -1 then (1 : ℂ) else if m = 0 then 2 else if m = 1 then 3 else 0) •
    Exp007.Controls.initialSpinor

private theorem active_coefficient_norms :
    ‖activeCoefficients (-1)‖ = 1 ∧ ‖activeCoefficients 0‖ = 2 ∧
      ‖activeCoefficients 1‖ = 3 := by
  norm_num [activeCoefficients, norm_smul, Exp007.Controls.initialSpinor_norm]

/-- All three signed modes are active, and the physical initial data is nonzero. -/
theorem active_signed_superposition :
    (∀ m ∈ activeSpectrum, |(m : ℝ)| ≤ 1 ∧ activeCoefficients m ≠ 0) ∧
    coefficientNorm activeSpectrum activeCoefficients = Real.sqrt 14 ∧
    finiteSolution activeSpectrum activeCoefficients 0 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    have hm' : m = -1 ∨ m = 0 ∨ m = 1 := by simpa [activeSpectrum] using hm
    rcases hm' with rfl | rfl | rfl
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.1]; norm_num)
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.2.1]; norm_num)
    · constructor
      · norm_num
      · exact norm_ne_zero_iff.mp (by rw [active_coefficient_norms.2.2]; norm_num)
  · norm_num [coefficientNorm, activeSpectrum, active_coefficient_norms.1,
      active_coefficient_norms.2.1, active_coefficient_norms.2.2]
  · intro hz
    have hc := congrArg (fun w : E 2 => w 0) hz
    norm_num [finiteSolution, activeSpectrum, modeSolution_initial,
      activeCoefficients, Exp007.Controls.initialSpinor] at hc

/-- A concrete admissible cutoff-one, eight-point grid with positive timestep. -/
theorem admissible_multimode_grid :
    2 * (1 : ℕ) < 7 + 1 ∧
    (0 : ℝ) < Real.pi / 4 ∧ Real.pi / 4 ≤ 1 ∧
    ((7 + 1 : ℕ) : ℝ) * (Real.pi / 4) = 2 * Real.pi ∧
    (0 : ℝ) < 1 / 12 ∧ 2 * (1 / 12 : ℝ) * ((1 : ℝ)^2 + 2) ≤ 1 := by
  refine ⟨by norm_num, by positivity, ?_, ?_, by norm_num, by norm_num⟩
  · linarith [Real.pi_le_four]
  · norm_num <;> ring

/-- Frequencies separated by the grid size produce the same sampled mode. -/
theorem grid_size_alias (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    modeLift n h 0 v = modeLift n h ((n + 1 : ℕ) : ℤ) v := by
  ext p
  simp only [modeLift, WithLp.ofLp_toLp, Int.cast_zero, Int.cast_natCast]
  have hp : Exp006.phase (((n + 1 : ℕ) : ℝ) * ((p.1.val : ℝ) * h)) = 1 := by
    rw [show ((n + 1 : ℕ) : ℝ) * ((p.1.val : ℝ) * h) =
      (p.1.val : ℝ) * (((n + 1 : ℕ) : ℝ) * h) by ring, hmesh]
    simpa using Exp006.phase_periodic.nat_mul_eq p.1.val
  simp only [Nat.cast_add, Nat.cast_one] at hp
  simp [hp]

/-- Opposite coefficients cancel on aliased modes, invalidating unrestricted Parseval. -/
theorem aliasing_breaks_naive_parseval (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) :
    ‖modeLift n h 0 Exp007.Controls.initialSpinor -
      modeLift n h ((n + 1 : ℕ) : ℤ) Exp007.Controls.initialSpinor‖^2 ≠
      ((n + 1 : ℕ) : ℝ) * (‖Exp007.Controls.initialSpinor‖^2 +
        ‖-Exp007.Controls.initialSpinor‖^2) := by
  rw [grid_size_alias n h hmesh]
  simp [Exp007.Controls.initialSpinor_norm] <;> positivity

/-- No time steps means the entire supplied initial grid error remains. -/
theorem empty_trajectory_retains_initial_error (n : ℕ) (h k : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2) (initial : Vec (Grid n)) :
    finiteGridError n h k 0 S a initial = finiteInitialError n h S a initial := by
  simp [finiteGridError, finiteInitialError]

/-- Superposition does not remove the actual noncommuting full-grid split. -/
theorem full_grid_split_is_noncommuting (n : ℕ) (h : ℝ) :
    ¬ Commute (hamiltonian n h Exp007.Z) (potential n Exp007.X) := by
  apply hamiltonian_noncommutes_potential
  simpa [Exp007.A, Exp007.B] using Exp007.A_noncommutes_B 0

/-- The constants are uniform in the mesh, but grow with the fixed frequency cutoff. -/
theorem frequency_constants_increase : Ct 1 < Ct 2 ∧ Cs 1 < Cs 2 := by
  norm_num [Ct, Cs]

#print axioms active_signed_superposition
#print axioms admissible_multimode_grid
#print axioms grid_size_alias
#print axioms aliasing_breaks_naive_parseval
#print axioms empty_trajectory_retains_initial_error
#print axioms full_grid_split_is_noncommuting
#print axioms frequency_constants_increase
end NDEAEvolve.Exp008.Controls
