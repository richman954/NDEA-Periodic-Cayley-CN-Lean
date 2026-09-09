import GenericUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact examples exercise variable spatial potential, nonzero forcing,
and the positivity condition used by energy separation. -/
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp013.Controls

def profile (x : ℝ) : ℂ := ((2 + Real.sin x : ℝ) : ℂ)
def stationarySolution (_t x : ℝ) : ℂ := profile x
def spatialPotential (_t x : ℝ) : ℂ →L[ℂ] ℂ :=
  (((-Real.sin x / (2 + Real.sin x) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ ℂ

private theorem stationarySolution_slice (t : ℝ) : stationarySolution t = profile := rfl

private theorem profile_hasDerivAt (x : ℝ) :
    HasDerivAt profile ((Real.cos x : ℝ) : ℂ) x := by
  simpa only [profile] using! ((Real.hasDerivAt_sin x).const_add 2).ofReal_comp

private theorem profile_deriv (x : ℝ) : deriv profile x = (Real.cos x : ℂ) :=
  (profile_hasDerivAt x).deriv

private theorem profile_second_hasDerivAt (x : ℝ) :
    HasDerivAt (deriv profile) ((-Real.sin x : ℝ) : ℂ) x := by
  rw [show deriv profile = (fun y : ℝ => (Real.cos y : ℂ)) from funext profile_deriv]
  exact (Real.hasDerivAt_cos x).ofReal_comp

private theorem profile_second_deriv (x : ℝ) :
    deriv (deriv profile) x = ((-Real.sin x : ℝ) : ℂ) :=
  (profile_second_hasDerivAt x).deriv

private theorem profile_denominator_ne_zero (x : ℝ) : 2 + Real.sin x ≠ 0 := by
  have h := Real.neg_one_le_sin x
  linarith

theorem spatialPotential_selfadjoint (t x : ℝ) : IsSelfAdjoint (spatialPotential t x) := by
  have hr : IsSelfAdjoint (((-Real.sin x / (2 + Real.sin x) : ℝ) : ℂ)) := by
    simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  exact hr.smul (IsSelfAdjoint.one (ℂ →L[ℂ] ℂ))

theorem spatialPotential_periodic (t : ℝ) :
    Function.Periodic (spatialPotential t) (2 * Real.pi) := by
  intro x
  simp [spatialPotential, Real.sin_add_two_pi]

theorem spatialPotential_continuous :
    Continuous (fun p : ℝ × ℝ => spatialPotential p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => -Real.sin p.2 / (2 + Real.sin p.2)) :=
    (Real.continuous_sin.comp continuous_snd).neg.div
      (continuous_const.add (Real.continuous_sin.comp continuous_snd))
      (fun p => profile_denominator_ne_zero p.2)
  exact (Complex.continuous_ofReal.comp h).smul continuous_const

theorem stationary_classical :
    IsClassicalPeriodicSolution (2 * Real.pi) spatialPotential 0 stationarySolution where
  time_differentiable t x := differentiableAt_const _
  space_differentiable t x := (profile_hasDerivAt x).differentiableAt
  second_space_differentiable t x := (profile_second_hasDerivAt x).differentiableAt
  continuous_solution := Complex.continuous_ofReal.comp
    (continuous_const.add (Real.continuous_sin.comp continuous_snd))
  continuous_time_derivative := by
    simpa only [stationarySolution, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_space_derivative := by
    simpa only [stationarySolution_slice, profile_deriv, Function.comp_def] using!
      (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))))
  continuous_second_derivative := by
    simpa only [stationarySolution_slice, profile_second_deriv, Function.comp_def] using!
      (Complex.continuous_ofReal.comp
        ((Real.continuous_sin.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))).neg))
  periodic t x := by simp [stationarySolution, profile, Real.sin_add_two_pi]
  schrodinger t x := by
    have hden := profile_denominator_ne_zero x
    simp only [stationarySolution_slice, deriv_const', profile_second_deriv,
      spatialPotential, _root_.smul_apply, ContinuousLinearMap.id_apply,
      Pi.zero_apply, add_zero, profile, smul_eq_mul]
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hden]
    simp

theorem stationary_nonzero (t x : ℝ) : stationarySolution t x ≠ 0 := by
  change ((2 + Real.sin x : ℝ) : ℂ) ≠ 0
  exact_mod_cast profile_denominator_ne_zero x

theorem stationary_nonconstant : stationarySolution 0 0 ≠ stationarySolution 0 (Real.pi / 2) := by
  norm_num [stationarySolution, profile, Real.sin_pi_div_two]

theorem spatialPotential_nonconstant : spatialPotential 0 0 ≠ spatialPotential 0 (Real.pi / 2) := by
  intro h
  have h1 := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  norm_num [spatialPotential, Real.sin_pi_div_two] at h1

theorem spatialPotential_active :
    spatialPotential 0 (Real.pi / 2) (stationarySolution 0 (Real.pi / 2)) = -1 := by
  norm_num [spatialPotential, stationarySolution, profile, Real.sin_pi_div_two]

def linearSolution (t _x : ℝ) : ℂ := (t : ℂ)
def constantForcing (_t _x : ℝ) : ℂ := Complex.I

private theorem linearSolution_slice (t : ℝ) :
    linearSolution t = (fun _ : ℝ => (t : ℂ)) := rfl

private theorem linear_time_derivative (t x : ℝ) :
    deriv (fun s => linearSolution s x) t = 1 := by
  simpa only [linearSolution, id_eq, Complex.ofReal_one] using!
    (hasDerivAt_id t).ofReal_comp.deriv

theorem forced_linear_classical (L : ℝ) :
    IsClassicalPeriodicSolution L 0 constantForcing linearSolution where
  time_differentiable t x := (hasDerivAt_id t).ofReal_comp.differentiableAt
  space_differentiable t x := differentiableAt_const _
  second_space_differentiable t x := by
    simpa only [linearSolution_slice, deriv_const'] using
      (differentiableAt_const (0 : ℂ) : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) x)
  continuous_solution := Complex.continuous_ofReal.comp continuous_fst
  continuous_time_derivative := by
    simpa only [linear_time_derivative] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℂ)))
  continuous_space_derivative := by
    simpa only [linearSolution_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_second_derivative := by
    simpa only [linearSolution_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  periodic t x := rfl
  schrodinger t x := by
    rw [linear_time_derivative]
    simp [linearSolution_slice, constantForcing]

theorem forcing_work_sign : forcingWork constantForcing linearSolution 1 0 = 2 := by
  norm_num [forcingWork, constantForcing, linearSolution, inner, RCLike.inner_apply]

theorem forcing_changes_norm : ‖linearSolution 0 0‖ ≠ ‖linearSolution 1 0‖ := by
  norm_num [linearSolution]

/-- Equal initial data and potential do not identify solutions when the
forcing differs. Both examples are classical on the same positive period. -/
theorem same_data_different_forcing :
    IsClassicalPeriodicSolution 1 0 constantForcing linearSolution ∧
      IsClassicalPeriodicSolution (H := ℂ) 1 0 0 0 ∧
      (∀ x : ℝ, linearSolution 0 x = 0) ∧ linearSolution 1 0 ≠ 0 := by
  refine ⟨forced_linear_classical 1, classical_zero 1 0, ?_, ?_⟩
  · intro x
    simp [linearSolution]
  · norm_num [linearSolution]

theorem zero_period_fails_separation :
    (∀ b : ℝ, (∫ _ in b..b+(0:ℝ), ‖(1 : ℂ)‖^2) = 0) ∧
      (fun _ : ℝ => (1 : ℂ)) ≠ 0 := by
  constructor
  · intro b
    simp
  · intro h
    have h0 := congrFun h 0
    norm_num at h0

/-- The generic conservation theorem applies to the active variable potential. -/
theorem stationary_energy_conserved (b s t : ℝ) :
    energy stationarySolution b (2 * Real.pi) s =
      energy stationarySolution b (2 * Real.pi) t :=
  energy_eq stationarySolution stationary_classical spatialPotential_selfadjoint b s t

theorem stationary_unique (u : ℝ → ℝ → ℂ)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) spatialPotential 0 u)
    (s : ℝ) (hs : ∀ x, u s x = profile x) : u = stationarySolution :=
  classical_unique_at_time (by positivity) u stationarySolution hu stationary_classical
    spatialPotential_selfadjoint s hs

theorem forcing_work_eq (t x : ℝ) :
    forcingWork constantForcing linearSolution t x = 2 * t := by
  simp [forcingWork, constantForcing, linearSolution, smul_eq_mul, RCLike.inner_apply]

theorem forced_energy_formula (b L t : ℝ) :
    energy linearSolution b L t = L * t^2 := by
  simp [energy, linearSolution, smul_eq_mul, pow_two]
  ring

/-- The general work identity gives the actual derivative of the forced mass. -/
theorem forced_energy_derivative (b L t : ℝ) :
    HasDerivAt (energy linearSolution b L) (L * (2 * t)) t := by
  have hV : ∀ s x : ℝ, IsSelfAdjoint ((0 : ℝ → ℝ → ℂ →L[ℂ] ℂ) s x) := by
    intro s x
    exact IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)
  simpa [forcing_work_eq, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    energy_time_hasDerivAt_work linearSolution (forced_linear_classical L) hV b t

end NDEAEvolve.Exp013.Controls
