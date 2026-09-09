import VariablePotentialBridge
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact controls use actual periodic fields and their calculated PDE
residuals. The linearly growing complex field saturates the coefficient-one
bound; stationary and zero fields check initial-error and zero-energy edges. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp015.Controls

def linearField (t _x : ℝ) : ℂ := (t : ℂ)

def constantField (c : ℂ) (_t _x : ℝ) : ℂ := c

private theorem controls_linear_slice (t : ℝ) :
    linearField t = (fun _ : ℝ => (t : ℂ)) := rfl

private theorem controls_linear_time_derivative (t x : ℝ) :
    deriv (fun s => linearField s x) t = 1 := by
  simpa only [linearField, id_eq, Complex.ofReal_one] using!
    (hasDerivAt_id t).ofReal_comp.deriv

private theorem controls_constant_slice (c : ℂ) (t : ℝ) :
    constantField c t = (fun _ : ℝ => c) := rfl

theorem linearField_regular (L : ℝ) : IsRegularPeriodicField L linearField where
  time_differentiable t x := (hasDerivAt_id t).ofReal_comp.differentiableAt
  space_differentiable t x := differentiableAt_const _
  second_space_differentiable t x := by
    simpa only [controls_linear_slice, deriv_const'] using
      (differentiableAt_const (0 : ℂ) : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) x)
  continuous_solution := Complex.continuous_ofReal.comp continuous_fst
  continuous_time_derivative := by
    simpa only [controls_linear_time_derivative] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℂ)))
  continuous_space_derivative := by
    simpa only [controls_linear_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_second_derivative := by
    simpa only [controls_linear_slice, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  periodic t x := rfl

theorem linearField_residual (t x : ℝ) :
    pdeResidual 0 linearField t x = Complex.I := by
  unfold pdeResidual
  rw [controls_linear_time_derivative]
  simp [controls_linear_slice]

theorem linearField_residual_continuous :
    Continuous (fun p : ℝ × ℝ => pdeResidual 0 linearField p.1 p.2) := by
  simpa only [linearField_residual] using
    (continuous_const : Continuous (fun _ : ℝ × ℝ => Complex.I))

theorem linearField_initial_zero (x : ℝ) : linearField 0 x = 0 := by
  simp [linearField]

theorem linearField_at_one (x : ℝ) : linearField 1 x = 1 := by
  simp [linearField]

theorem linearField_l2 (t b : ℝ) : spatialL2 (linearField t) b 1 = |t| := by
  rw [controls_linear_slice]
  simpa only [Real.sqrt_one, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    spatialL2_const (t : ℂ) b 1 (by norm_num)

theorem linearField_residual_l2 (t b : ℝ) :
    spatialL2 (pdeResidual 0 linearField t) b 1 = 1 := by
  have he : pdeResidual 0 linearField t = (fun _ : ℝ => Complex.I) :=
    funext fun x => linearField_residual t x
  rw [he, spatialL2_const Complex.I b 1 (by norm_num)]
  simp

theorem linearField_residual_integral :
    (∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 linearField r) 0 1) = 1 := by
  simp [linearField_residual_l2]

theorem linearField_saturates_bound :
    spatialL2 (linearField 1) 0 1 = spatialL2 (linearField 0) 0 1 +
      ∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 linearField r) 0 1 := by
  rw [linearField_l2, linearField_l2, linearField_residual_integral]
  norm_num

theorem linearField_certified_error :
    spatialL2 (linearField 1) 0 1 ≤ spatialL2 (linearField 0) 0 1 +
      ∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 linearField r) 0 1 := by
  have h := residual_error_continuous_potential linearField (0 : ℝ → ℝ → ℂ)
    (linearField_regular 1) (Exp013.classical_zero 1 (0 : ℝ → ℝ → ℂ →L[ℂ] ℂ))
    (fun _ _ => IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)) (by norm_num : (0 : ℝ) < 1)
    (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ →L[ℂ] ℂ)))
    0 0 1 (by norm_num)
  simpa only [Pi.zero_apply, sub_zero] using h

theorem linearField_coefficient_one_required (C : ℝ)
    (h : spatialL2 (linearField 1) 0 1 ≤ C *
      ∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 linearField r) 0 1) : 1 ≤ C := by
  simpa [linearField_l2, linearField_residual_integral] using h

theorem linearField_certified_exact_initialization :
    spatialL2 (linearField 1) 0 1 ≤
      ∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 linearField r) 0 1 := by
  have h := residual_error_exact_initialization linearField (0 : ℝ → ℝ → ℂ)
    (linearField_regular 1) (Exp013.classical_zero 1 (0 : ℝ → ℝ → ℂ →L[ℂ] ℂ))
    (fun _ _ => IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)) (by norm_num : (0 : ℝ) < 1)
    linearField_residual_continuous 0 0 1 (by norm_num)
    (fun x => linearField_initial_zero x)
  simpa only [Pi.zero_apply, sub_zero] using h

theorem constantField_regular (c : ℂ) (L : ℝ) :
    IsRegularPeriodicField L (constantField c) where
  time_differentiable t x := differentiableAt_const _
  space_differentiable t x := differentiableAt_const _
  second_space_differentiable t x := by
    simpa only [controls_constant_slice, deriv_const'] using
      (differentiableAt_const (0 : ℂ) : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) x)
  continuous_solution := continuous_const
  continuous_time_derivative := by
    simpa only [constantField, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_space_derivative := by
    simpa only [controls_constant_slice, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  continuous_second_derivative := by
    simpa only [controls_constant_slice, deriv_const', deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ)))
  periodic t x := rfl

theorem constantField_residual (c : ℂ) (t x : ℝ) :
    pdeResidual 0 (constantField c) t x = 0 := by
  simp [pdeResidual, controls_constant_slice, constantField]

theorem constantField_l2 (c : ℂ) (t b : ℝ) :
    spatialL2 (constantField c t) b 1 = ‖c‖ := by
  rw [controls_constant_slice]
  simpa only [Real.sqrt_one, one_mul] using
    spatialL2_const c b 1 (by norm_num)

theorem constantField_initial_error_preserved (t : ℝ) :
    spatialL2 (constantField 1 t) 0 1 = spatialL2 (constantField 1 0) 0 1 ∧
      spatialL2 (constantField 1 0) 0 1 = 1 := by
  simp [constantField_l2]

theorem constantField_residual_integral (c : ℂ) (s t : ℝ) :
    (∫ r in s..t, spatialL2 (pdeResidual 0 (constantField c) r) 0 1) = 0 := by
  have he (r : ℝ) : pdeResidual 0 (constantField c) r = (0 : ℝ → ℂ) :=
    funext fun x => constantField_residual c r x
  simp only [he, spatialL2_zero, intervalIntegral.integral_zero]

theorem constantField_certified_error (s t : ℝ) (hst : s ≤ t) :
    spatialL2 (constantField 1 t) 0 1 ≤ spatialL2 (constantField 1 s) 0 1 +
      ∫ r in s..t, spatialL2 (pdeResidual 0 (constantField 1) r) 0 1 := by
  have h := residual_error_continuous_potential (constantField 1) (0 : ℝ → ℝ → ℂ)
    (constantField_regular 1 1) (Exp013.classical_zero 1 (0 : ℝ → ℝ → ℂ →L[ℂ] ℂ))
    (fun _ _ => IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)) (by norm_num : (0 : ℝ) < 1)
    (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ →L[ℂ] ℂ)))
    0 s t hst
  simpa only [Pi.zero_apply, sub_zero] using h

theorem constantField_initial_error_cannot_be_omitted :
    ¬(spatialL2 (constantField 1 1) 0 1 ≤
      ∫ r in (0 : ℝ)..1, spatialL2 (pdeResidual 0 (constantField 1) r) 0 1) := by
  simp [constantField_l2, constantField_residual_integral]

theorem zeroField_zero_energy (t : ℝ) :
    Exp013.energy (0 : ℝ → ℝ → ℂ) 0 1 t = 0 := by
  simp [Exp013.energy]

theorem zeroField_certified_error (s t : ℝ) (hst : s ≤ t) :
    spatialL2 (0 : ℝ → ℂ) 0 1 ≤ spatialL2 (0 : ℝ → ℂ) 0 1 +
      ∫ r in s..t, spatialL2 (pdeResidual 0 (0 : ℝ → ℝ → ℂ) r) 0 1 := by
  have h := residual_error_continuous_potential (0 : ℝ → ℝ → ℂ) (0 : ℝ → ℝ → ℂ)
    (regular_zero 1) (Exp013.classical_zero 1 (0 : ℝ → ℝ → ℂ →L[ℂ] ℂ))
    (fun _ _ => IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)) (by norm_num : (0 : ℝ) < 1)
    (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℂ →L[ℂ] ℂ)))
    0 s t hst
  simpa only [Pi.zero_apply, sub_zero, Pi.zero_def] using h

theorem linearField_time_zero_bound :
    spatialL2 (linearField 0) 0 1 = spatialL2 (linearField 0) 0 1 +
      ∫ r in (0 : ℝ)..0, spatialL2 (pdeResidual 0 linearField r) 0 1 := by
  simp

end NDEAEvolve.Exp015.Controls
