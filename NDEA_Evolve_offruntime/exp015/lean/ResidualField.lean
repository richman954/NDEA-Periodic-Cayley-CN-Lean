import GenericClassical

/-! An approximate field is required to have actual classical derivatives.
Its residual is calculated from those derivatives and the given potential. -/
noncomputable section
namespace NDEAEvolve.Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure IsRegularPeriodicField (L : ℝ) (u : ℝ → ℝ → H) : Prop where
  time_differentiable : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space_differentiable : ∀ t x, DifferentiableAt ℝ (u t) x
  second_space_differentiable : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x
  continuous_solution : Continuous (fun p : ℝ × ℝ => u p.1 p.2)
  continuous_time_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1)
  continuous_space_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)
  continuous_second_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (u p.1)) p.2)
  periodic : ∀ t, Function.Periodic (u t) L

def pdeResidual (V : ℝ → ℝ → H →L[ℂ] H) (u : ℝ → ℝ → H) (t x : ℝ) : H :=
  Complex.I • deriv (fun s => u s x) t + deriv (deriv (u t)) x - V t x (u t x)

theorem classical_regular {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H}
    {f u : ℝ → ℝ → H} (hu : Exp013.IsClassicalPeriodicSolution L V f u) :
    IsRegularPeriodicField L u where
  time_differentiable := hu.time_differentiable
  space_differentiable := hu.space_differentiable
  second_space_differentiable := hu.second_space_differentiable
  continuous_solution := hu.continuous_solution
  continuous_time_derivative := hu.continuous_time_derivative
  continuous_space_derivative := hu.continuous_space_derivative
  continuous_second_derivative := hu.continuous_second_derivative
  periodic := hu.periodic

theorem regular_classical_residual {L : ℝ} (V : ℝ → ℝ → H →L[ℂ] H)
    (u : ℝ → ℝ → H) (hu : IsRegularPeriodicField L u) :
    Exp013.IsClassicalPeriodicSolution L V (pdeResidual V u) u where
  time_differentiable := hu.time_differentiable
  space_differentiable := hu.space_differentiable
  second_space_differentiable := hu.second_space_differentiable
  continuous_solution := hu.continuous_solution
  continuous_time_derivative := hu.continuous_time_derivative
  continuous_space_derivative := hu.continuous_space_derivative
  continuous_second_derivative := hu.continuous_second_derivative
  periodic := hu.periodic
  schrodinger t x := by unfold pdeResidual; abel

theorem classical_residual_eq_forcing {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H}
    {f u : ℝ → ℝ → H} (hu : Exp013.IsClassicalPeriodicSolution L V f u)
    (t x : ℝ) : pdeResidual V u t x = f t x := by
  unfold pdeResidual
  rw [hu.schrodinger t x]
  abel

theorem pdeResidual_continuous {L : ℝ} (V : ℝ → ℝ → H →L[ℂ] H)
    (u : ℝ → ℝ → H) (hu : IsRegularPeriodicField L u)
    (hV : Continuous (fun p : ℝ × ℝ => V p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => pdeResidual V u p.1 p.2) :=
  ((hu.continuous_time_derivative.const_smul Complex.I).add
    hu.continuous_second_derivative).sub (hV.clm_apply hu.continuous_solution)

theorem regular_zero (L : ℝ) : IsRegularPeriodicField L (0 : ℝ → ℝ → H) :=
  classical_regular (Exp013.classical_zero L (0 : ℝ → ℝ → H →L[ℂ] H))

theorem pdeResidual_zero (V : ℝ → ℝ → H →L[ℂ] H) (t x : ℝ) :
    pdeResidual V (0 : ℝ → ℝ → H) t x = 0 := by
  simp [pdeResidual]

end NDEAEvolve.Exp015
