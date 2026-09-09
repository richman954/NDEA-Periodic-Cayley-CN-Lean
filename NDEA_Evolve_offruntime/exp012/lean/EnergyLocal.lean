import Continuity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Local conservation for arbitrary classical periodic solutions. No Fourier
representation is assumed for the solution in these statements. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp010
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp012

def energyDensity (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ := ‖u t x‖ ^ 2

def densityDerivative (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (deriv (fun s => u s x) t)).re

def flux (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (u t) x)).re

theorem potential_selfadjoint :
    IsSelfAdjoint (operatorOf (Exp007.Z + Exp007.X)) := by
  change star (operatorOf (Exp007.Z + Exp007.X)) = _
  simpa only [operatorOf, map_star] using
    congrArg (fun M : Mat 2 => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M)
      (hermitian_star (Exp007.Z_isHermitian.add Exp007.X_isHermitian))

theorem potential_cancellation (w : E 2) :
    (inner ℂ w ((-Complex.I) • operatorOf (Exp007.Z + Exp007.X) w)).re = 0 := by
  have h := potential_selfadjoint.isSymmetric.im_inner_self_apply w
  change (inner ℂ w (operatorOf (Exp007.Z + Exp007.X) w)).im = 0 at h
  rw [inner_smul_right]
  simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, sub_neg_eq_add, zero_add, zero_sub, neg_neg] using h

theorem imaginary_self_cancellation (w : E 2) :
    (inner ℂ w (Complex.I • w)).re = 0 := by
  have h := inner_self_im (𝕜 := ℂ) w
  change (inner ℂ w w).im = 0 at h
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, h, sub_self]

theorem periodic_deriv {f : ℝ → E 2} {L : ℝ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have hd := (hf (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
  have he : (fun y => f (y + L)) = f := funext hp
  simpa only [Function.comp_def, id_eq, one_smul, he] using hd.deriv.symm

theorem density_time_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    HasDerivAt (fun s => energyDensity u s x) (densityDerivative u t x) t := by
  letI : InnerProductSpace ℝ (E 2) := InnerProductSpace.rclikeToReal ℂ (E 2)
  simpa only [energyDensity, densityDerivative, real_inner_eq_re_inner ℂ] using!
    (hu.time_differentiable t x).hasDerivAt.norm_sq

theorem energyDensity_continuous (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) :
    Continuous (fun p : ℝ × ℝ => energyDensity u p.1 p.2) :=
  hu.continuous_solution.norm.pow 2

theorem densityDerivative_continuous (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) :
    Continuous (fun p : ℝ × ℝ => densityDerivative u p.1 p.2) := by
  exact (Complex.continuous_re.comp
    (hu.continuous_solution.inner hu.continuous_time_derivative)).const_mul 2

theorem classical_time_derivative (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    deriv (fun s => u s x) t = Complex.I • deriv (deriv (u t)) x +
      (-Complex.I) • operatorOf (Exp007.Z + Exp007.X) (u t x) := by
  have h := congrArg (fun z : E 2 => (-Complex.I) • z) (hu.schrodinger t x)
  simpa [smul_add, smul_smul, smul_neg, neg_smul] using h

theorem densityDerivative_eq_spatial_expression (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    densityDerivative u t x =
      2 * (inner ℂ (u t x) (Complex.I • deriv (deriv (u t)) x)).re := by
  unfold densityDerivative
  rw [classical_time_derivative u hu t x]
  simp only [inner_add_right, Complex.add_re, potential_cancellation, add_zero]

/-- The spatial derivative of the periodic flux is the actual time derivative
of the squared solution norm. -/
theorem flux_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    HasDerivAt (flux u t) (densityDerivative u t x) x := by
  rw [densityDerivative_eq_spatial_expression u hu t x]
  have hd := (hu.space_differentiable t x).hasDerivAt.inner ℂ
    ((hu.second_space_differentiable t x).hasDerivAt.const_smul Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [flux, Complex.add_re, imaginary_self_cancellation] using! hr.const_mul 2

theorem flux_periodic (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t : ℝ) :
    Function.Periodic (flux u t) (2 * Real.pi) := by
  have hp := periodic_deriv (hu.space_differentiable t) (hu.periodic t)
  intro x
  simp only [flux, hu.periodic t x, hp x]

theorem classical_sub_time_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (fun s => u s x - v s x) t =
      deriv (fun s => u s x) t - deriv (fun s => v s x) t :=
  deriv_sub (hu.time_differentiable t x) (hv.time_differentiable t x)

theorem classical_sub_space_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (fun y => u t y - v t y) x = deriv (u t) x - deriv (v t) x :=
  deriv_sub (hu.space_differentiable t x) (hv.space_differentiable t x)

theorem classical_sub_second_derivative (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) (t x : ℝ) :
    deriv (deriv (fun y => u t y - v t y)) x =
      deriv (deriv (u t)) x - deriv (deriv (v t)) x := by
  have he : deriv (fun y => u t y - v t y) =
      fun y => deriv (u t) y - deriv (v t) y :=
    funext (classical_sub_space_derivative u v hu hv t)
  rw [he]
  exact deriv_sub (hu.second_space_differentiable t x) (hv.second_space_differentiable t x)

theorem classical_sub (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v) :
    IsClassicalPeriodicSolution (fun t x => u t x - v t x) where
  time_differentiable t x := (hu.time_differentiable t x).sub (hv.time_differentiable t x)
  space_differentiable t x := (hu.space_differentiable t x).sub (hv.space_differentiable t x)
  second_space_differentiable t x := by
    have he : deriv (fun y => u t y - v t y) =
        fun y => deriv (u t) y - deriv (v t) y :=
      funext (classical_sub_space_derivative u v hu hv t)
    rw [he]
    exact (hu.second_space_differentiable t x).sub (hv.second_space_differentiable t x)
  continuous_solution := hu.continuous_solution.sub hv.continuous_solution
  continuous_time_derivative := by
    simpa only [classical_sub_time_derivative u v hu hv] using
      hu.continuous_time_derivative.sub hv.continuous_time_derivative
  continuous_space_derivative := by
    simpa only [classical_sub_space_derivative u v hu hv] using
      hu.continuous_space_derivative.sub hv.continuous_space_derivative
  continuous_second_derivative := by
    simpa only [classical_sub_second_derivative u v hu hv] using
      hu.continuous_second_derivative.sub hv.continuous_second_derivative
  periodic t x := by simp only [hu.periodic t x, hv.periodic t x]
  schrodinger t x := by
    rw [classical_sub_time_derivative u v hu hv, classical_sub_second_derivative u v hu hv,
      smul_sub, hu.schrodinger t x, hv.schrodinger t x, map_sub]
    abel

theorem classical_zero : IsClassicalPeriodicSolution (fun _ _ : ℝ => (0 : E 2)) := by
  have ha : Regular (fun _ : ℤ => (0 : E 2)) := by simp [Regular]
  have he : Exp009.infiniteSolution (fun _ : ℤ => (0 : E 2)) =
      (fun _ _ : ℝ => (0 : E 2)) := by
    funext t x
    simp [Exp009.infiniteSolution, Exp008.modeSolution, Exp008.modeOrbit]
  simpa only [he] using infiniteSolution_classical (fun _ : ℤ => (0 : E 2)) ha

end NDEAEvolve.Exp012
