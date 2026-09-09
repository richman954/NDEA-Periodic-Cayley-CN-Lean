import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Classical periodic Schrödinger systems in a complex Hilbert space. The
potential and forcing may depend on time and position. Actual derivatives
and their joint continuity are required; no existence claim is built in. -/
noncomputable section
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp013

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Classical solution of `i u_t = -u_xx + V(t,x)u + f(t,x)`, periodic with
period `L`. Positivity of the period and symmetry of the potential are separate
hypotheses of the results that use them. -/
structure IsClassicalPeriodicSolution (L : ℝ) (V : ℝ → ℝ → H →L[ℂ] H)
    (f u : ℝ → ℝ → H) : Prop where
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
  schrodinger : ∀ t x, Complex.I • deriv (fun s => u s x) t =
    -deriv (deriv (u t)) x + V t x (u t x) + f t x

def energyDensity (u : ℝ → ℝ → H) (t x : ℝ) : ℝ := ‖u t x‖ ^ 2

def densityDerivative (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (deriv (fun s => u s x) t)).re

def flux (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (u t) x)).re

def fluxDerivative (u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (deriv (u t)) x)).re

def forcingWork (f u : ℝ → ℝ → H) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) ((-Complex.I) • f t x)).re

theorem potential_cancellation (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (w : H) :
    (inner ℂ w ((-Complex.I) • A w)).re = 0 := by
  have h := hA.isSymmetric.im_inner_self_apply w
  change (inner ℂ w (A w)).im = 0 at h
  rw [inner_smul_right]
  simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, sub_neg_eq_add, zero_add,
    zero_sub, neg_neg] using h

omit [CompleteSpace H] in
theorem imaginary_self_cancellation (w : H) :
    (inner ℂ w (Complex.I • w)).re = 0 := by
  have h := inner_self_im (𝕜 := ℂ) w
  change (inner ℂ w w).im = 0 at h
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, h, sub_self]

omit [CompleteSpace H] in
theorem periodic_deriv {g : ℝ → H} {L : ℝ}
    (hg : Differentiable ℝ g) (hp : Function.Periodic g L) :
    Function.Periodic (deriv g) L := by
  intro x
  have hd := (hg (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
  have he : (fun y => g (y + L)) = g := funext hp
  simpa only [Function.comp_def, id_eq, one_smul, he] using hd.deriv.symm

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f g : ℝ → ℝ → H}

omit [CompleteSpace H] in
theorem density_time_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    HasDerivAt (fun s => energyDensity u s x) (densityDerivative u t x) t := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  simpa only [energyDensity, densityDerivative, real_inner_eq_re_inner ℂ] using!
    (hu.time_differentiable t x).hasDerivAt.norm_sq

omit [CompleteSpace H] in
theorem energyDensity_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => energyDensity u p.1 p.2) :=
  hu.continuous_solution.norm.pow 2

omit [CompleteSpace H] in
theorem densityDerivative_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => densityDerivative u p.1 p.2) :=
  (Complex.continuous_re.comp
    (hu.continuous_solution.inner hu.continuous_time_derivative)).const_mul 2

omit [CompleteSpace H] in
theorem fluxDerivative_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) :
    Continuous (fun p : ℝ × ℝ => fluxDerivative u p.1 p.2) :=
  (Complex.continuous_re.comp
    (hu.continuous_solution.inner
      (hu.continuous_second_derivative.const_smul Complex.I))).const_mul 2

omit [CompleteSpace H] in
theorem classical_time_derivative (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    deriv (fun s => u s x) t = Complex.I • deriv (deriv (u t)) x +
      (-Complex.I) • V t x (u t x) + (-Complex.I) • f t x := by
  have h := congrArg (fun z : H => (-Complex.I) • z) (hu.schrodinger t x)
  simpa [smul_add, smul_smul, smul_neg, neg_smul] using h

/-- Pointwise forced mass balance. No differentiability of the potential or
forcing is used: the potential cancels by pointwise self-adjointness. -/
theorem densityDerivative_eq_fluxDerivative_add_forcingWork (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (t x : ℝ) :
    densityDerivative u t x = fluxDerivative u t x + forcingWork f u t x := by
  unfold densityDerivative fluxDerivative forcingWork
  rw [classical_time_derivative u hu t x]
  simp only [inner_add_right, Complex.add_re, potential_cancellation _ (hV t x), add_zero]
  ring

/-- Although no separate continuity of the forcing is assumed, its work along
a classical solution is continuous by the actual local balance identity. -/
theorem forcingWork_continuous (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) :
    Continuous (fun p : ℝ × ℝ => forcingWork f u p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => forcingWork f u p.1 p.2) =
      fun p => densityDerivative u p.1 p.2 - fluxDerivative u p.1 p.2 := by
    funext p
    linarith [densityDerivative_eq_fluxDerivative_add_forcingWork u hu hV p.1 p.2]
  rw [he]
  exact (densityDerivative_continuous u hu).sub (fluxDerivative_continuous u hu)

omit [CompleteSpace H] in
theorem flux_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t x : ℝ) :
    HasDerivAt (flux u t) (fluxDerivative u t x) x := by
  have hd := (hu.space_differentiable t x).hasDerivAt.inner ℂ
    ((hu.second_space_differentiable t x).hasDerivAt.const_smul Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [flux, fluxDerivative, Complex.add_re, imaginary_self_cancellation] using! hr.const_mul 2

omit [CompleteSpace H] in
theorem flux_periodic (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (t : ℝ) :
    Function.Periodic (flux u t) L := by
  have hp := periodic_deriv (hu.space_differentiable t) (hu.periodic t)
  intro x
  simp only [flux, hu.periodic t x, hp x]

omit [CompleteSpace H] in
theorem classical_sub_time_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (fun s => u s x - v s x) t =
      deriv (fun s => u s x) t - deriv (fun s => v s x) t :=
  deriv_sub (hu.time_differentiable t x) (hv.time_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub_space_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (fun y => u t y - v t y) x = deriv (u t) x - deriv (v t) x :=
  deriv_sub (hu.space_differentiable t x) (hv.space_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub_second_derivative (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) (t x : ℝ) :
    deriv (deriv (fun y => u t y - v t y)) x =
      deriv (deriv (u t)) x - deriv (deriv (v t)) x := by
  have he : deriv (fun y => u t y - v t y) =
      fun y => deriv (u t) y - deriv (v t) y :=
    funext (classical_sub_space_derivative u v hu hv t)
  rw [he]
  exact deriv_sub (hu.second_space_differentiable t x) (hv.second_space_differentiable t x)

omit [CompleteSpace H] in
theorem classical_sub (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V g v) :
    IsClassicalPeriodicSolution L V (fun t x => f t x - g t x)
      (fun t x => u t x - v t x) where
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

omit [CompleteSpace H] in
theorem classical_sub_same_forcing (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v) :
    IsClassicalPeriodicSolution L V 0 (fun t x => u t x - v t x) := by
  simpa only [sub_self, Pi.zero_def] using classical_sub u v hu hv

omit [CompleteSpace H] in
theorem classical_zero (L : ℝ) (V : ℝ → ℝ → H →L[ℂ] H) :
    IsClassicalPeriodicSolution L V 0 0 where
  time_differentiable _ _ := differentiableAt_const _
  space_differentiable _ _ := differentiableAt_const _
  second_space_differentiable _ x := by
    simpa only [Pi.zero_def, deriv_const'] using
      (differentiableAt_const (0 : H) : DifferentiableAt ℝ (fun _ : ℝ => (0 : H)) x)
  continuous_solution := continuous_const
  continuous_time_derivative := by
    simpa only [Pi.zero_def, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  continuous_space_derivative := by
    simpa only [Pi.zero_def, deriv_const] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  continuous_second_derivative := by
    simpa only [Pi.zero_def, deriv_const'] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : H)))
  periodic _ _ := rfl
  schrodinger _ _ := by simp [Pi.zero_def, deriv_const]

end NDEAEvolve.Exp013
