import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Module

-- SOURCE lean/Exp013GenericFoundation.lean SHA256 dad2f80daceb0c14eaa7c68a9d7397eb6eb75da989ca4c951b5aaf1af188d959

-- SOURCE predecessor_sources/GenericClassical.lean SHA256 26198a2e7dbc815ef665c663c1c3c991cba5926a67ac1e5361530db1c4ee33ec

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


-- SOURCE predecessor_sources/GenericEnergy.lean SHA256 f1668d4704a8527839e8ffec5fff535b923c12e28285be7434ac62045d64dece

/-! Energy balance and homogeneous conservation in a complex Hilbert space.
The derivative majorant is obtained on local compact rectangles. The potential
may vary in time and position; only its pointwise self-adjointness is used. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval
namespace NDEAEvolve.Exp013

theorem compact_derivative_bound (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b t : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Ioo (t-1) (t+1), ∀ x ∈ uIcc a b, ‖g s x‖ ≤ C := by
  have hcompact : IsCompact (Icc (t-1) (t+1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C,?_⟩
  intro s hs x hx
  exact hC (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩

theorem joint_interval_hasDerivAt (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hd : ∀ s x, HasDerivAt (fun t => f t x) (g s x) s) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f s x) (∫ x in a..b, g t x) t := by
  obtain ⟨C,hC⟩ := compact_derivative_bound g hg a b t
  have hf_slice (s : ℝ) : Continuous (f s) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hg_slice (s : ℝ) : Continuous (g s) :=
    hg.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := g) (a := a) (b := b)
    (s := Ioo (t-1) (t+1)) (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall fun s => (hf_slice s).aestronglyMeasurable
  · exact (hf_slice t).intervalIntegrable a b
  · exact (hg_slice t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x hx s hs => hC s hs x (uIoc_subset_uIcc hx)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ s _ => hd s x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energy (u : ℝ → ℝ → H) (b L t : ℝ) : ℝ :=
  ∫ x in b..b+L, ‖u t x‖^2

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem energy_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fun x => ‖u t x‖^2) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (energyDensity u t) := (energyDensity_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem densityDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (densityDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (densityDerivative u t) := (densityDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem fluxDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fluxDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fluxDerivative u t) := (fluxDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem forcingWork_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    IntervalIntegrable (forcingWork f u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (forcingWork f u t) := (forcingWork_continuous u hu hV).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem energy_time_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, densityDerivative u t x) t :=
  joint_interval_hasDerivAt (energyDensity u) (densityDerivative u)
    (energyDensity_continuous u hu) (densityDerivative_continuous u hu)
    (density_time_hasDerivAt u hu) b (b+L) t

theorem fluxDerivative_integral_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    (∫ x in b..b+L, fluxDerivative u t x) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux u t) (f' := fluxDerivative u t) (a := b) (b := b+L)
    (fun x _ => flux_hasDerivAt u hu t x) (fluxDerivative_intervalIntegrable u hu b t)
  rw [flux_periodic u hu t b, sub_self] at h
  exact h

theorem densityDerivative_integral_eq_forcingWork (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    (∫ x in b..b+L, densityDerivative u t x) = ∫ x in b..b+L, forcingWork f u t x := by
  calc
    (∫ x in b..b+L, densityDerivative u t x) =
        ∫ x in b..b+L, fluxDerivative u t x + forcingWork f u t x :=
      intervalIntegral.integral_congr
        (fun x _ => densityDerivative_eq_fluxDerivative_add_forcingWork u hu hV t x)
    _ = (∫ x in b..b+L, fluxDerivative u t x) +
        ∫ x in b..b+L, forcingWork f u t x :=
      intervalIntegral.integral_add (fluxDerivative_intervalIntegrable u hu b t)
        (forcingWork_intervalIntegrable u hu hV b t)
    _ = ∫ x in b..b+L, forcingWork f u t x := by
      rw [fluxDerivative_integral_zero u hu b t, zero_add]

theorem energy_time_hasDerivAt_work (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, forcingWork f u t x) t := by
  have h := energy_time_hasDerivAt u hu b t
  rw [densityDerivative_integral_eq_forcingWork u hu hV b t] at h
  exact h

theorem energy_hasDerivAt_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) 0 t := by
  simpa [forcingWork] using energy_time_hasDerivAt_work u hu hV b t

theorem energy_eq (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    energy u b L s = energy u b L t :=
  is_const_of_deriv_eq_zero (f := energy u b L)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).deriv) s t

theorem energy_eq_initial (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    energy u b L t = energy u b L 0 :=
  energy_eq u hu hV b t 0

end NDEAEvolve.Exp013


-- SOURCE predecessor_sources/GenericUniqueness.lean SHA256 93d1fed2c93b69ff1d9614faaef4a7150e0a392cbe9e206e88b1cfefd451cab9

/-! Uniqueness within the classical periodic solution class for a common
time- and space-dependent self-adjoint potential and common forcing. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp013

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sq_integral_pos_of_ne_zero (w : ℝ → H) (hw : Continuous w)
    (b L : ℝ) (hL : 0 < L) (hb : w b ≠ 0) :
    0 < ∫ x in b..b+L, ‖w x‖^2 := by
  apply intervalIntegral.integral_pos (by linarith : b < b+L)
    (hw.norm.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · refine ⟨b, ⟨le_refl _, by linarith⟩, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem norm_sq_integrals_separate_zero (w : ℝ → H) (hw : Continuous w)
    (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖w x‖^2) = 0) : w = 0 := by
  funext x
  by_contra hx
  have hp := norm_sq_integral_pos_of_ne_zero w hw x L hL hx
  rw [hz x] at hp
  exact lt_irrefl 0 hp

theorem norm_sq_integrals_separate (u v : ℝ → H)
    (hu : Continuous u) (hv : Continuous v) (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖u x-v x‖^2) = 0) : u = v := by
  have h := norm_sq_integrals_separate_zero (fun x => u x-v x) (hu.sub hv) L hL hz
  funext x
  exact sub_eq_zero.mp (congrFun h x)

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem classical_difference_energy_conserved (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    (∫ x in b..b+L, ‖u s x-v s x‖^2) = ∫ x in b..b+L, ‖u t x-v t x‖^2 :=
  energy_eq (fun r x => u r x-v r x) (classical_sub_same_forcing u v hu hv) hV b s t

theorem classical_unique_at_time (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x))
    (s : ℝ) (hs : ∀ x, u s x = v s x) : u = v := by
  funext t
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  apply norm_sq_integrals_separate (u t) (v t)
    (hu.continuous_solution.comp hp) (hv.continuous_solution.comp hp) L hL
  intro b
  have h := classical_difference_energy_conserved u v hu hv hV b t s
  simpa [hs] using h

theorem classical_unique (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = v 0 x) : u = v :=
  classical_unique_at_time hL u v hu hv hV 0 h0

theorem classical_zero_of_time_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (s : ℝ) (hs : ∀ x, u s x = 0) : u = 0 :=
  classical_unique_at_time hL u 0 hu (classical_zero L V) hV s hs

theorem classical_zero_of_initial_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = 0) : u = 0 :=
  classical_zero_of_time_zero hL u hu hV 0 h0

end NDEAEvolve.Exp013



-- SOURCE lean/StrongOperatorDerivative.lean SHA256 418ca3c3ac6f4cfcd3b8a3e05230eea922a6c95656c04b806ff743abc2b90e36

/-! Differentiation with a strongly continuous operator family. This does not
require differentiability, or even continuity, in the operator norm. -/
noncomputable section
open Filter
open scoped Topology
namespace NDEAEvolve.Exp014

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem strong_apply_hasDerivAt (A : ℝ → E →L[ℝ] F)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2))
    (b : ℝ → E) (b' : E) (c' : F) (t : ℝ)
    (hb : HasDerivAt b b' t)
    (hc : HasDerivAt (fun s => A s (b t)) c' t) :
    HasDerivAt (fun s => A s (b s)) (A t b' + c') t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hi : Tendsto (fun s : ℝ => s) (𝓝[≠] t) (𝓝 t) := nhdsWithin_le_nhds
  have hfirst : Tendsto (fun s => A s (slope b t s))
      (𝓝[≠] t) (𝓝 (A t b')) :=
    (hA.tendsto (t,b')).comp (hi.prodMk_nhds hb.tendsto_slope)
  have hsum := hfirst.add hc.tendsto_slope
  convert hsum using 1
  funext s
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  module

end NDEAEvolve.Exp014


-- SOURCE lean/GlobalLinearEvolution.lean SHA256 93a0f239ecb2707d4296681669fd8c5ce6b3f03bd91d6dff07a04c532b9fdac1

/-! Global evolution for a uniformly bounded, time-dependent linear ODE.
The Dyson series is constructed by actual iterated interval integrals. Its
factorial bound and locally uniform derivative bounds justify differentiation
at every real time, including negative time. -/

noncomputable section
open scoped Topology BigOperators NNReal
open Set MeasureTheory intervalIntegral

namespace NDEAEvolve.Exp014

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def dysonTerm (A : ℝ → E →L[ℝ] E) (x₀ : E) : ℕ → ℝ → E
  | 0, _ => x₀
  | n + 1, t => ∫ s in 0..t, A s (dysonTerm A x₀ n s)

theorem dysonTerm_continuous (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2)) (x₀ : E) (n : ℕ) :
    Continuous (dysonTerm A x₀ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n hn =>
    have hc : Continuous (fun t => A t (dysonTerm A x₀ n t)) :=
      hA.comp (continuous_id.prodMk hn)
    exact continuous_primitive (fun a b => hc.intervalIntegrable a b) 0

theorem dysonTerm_succ_hasDerivAt (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2)) (x₀ : E) (n : ℕ) (t : ℝ) :
    HasDerivAt (dysonTerm A x₀ (n + 1)) (A t (dysonTerm A x₀ n t)) t := by
  have hc : Continuous (fun s => A s (dysonTerm A x₀ n s)) :=
    hA.comp (continuous_id.prodMk (dysonTerm_continuous A hA x₀ n))
  exact integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt

theorem dysonTerm_succ_zero (A : ℝ → E →L[ℝ] E) (x₀ : E) (n : ℕ) :
    dysonTerm A x₀ (n + 1) 0 = 0 := by
  simp [dysonTerm]

theorem dysonTerm_norm_le (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (n : ℕ) (t : ℝ) :
    ‖dysonTerm A x₀ n t‖ ≤ (K * |t|) ^ n / n.factorial * ‖x₀‖ := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n hn =>
    change ‖∫ s in 0..t, A s (dysonTerm A x₀ n s)‖ ≤ _
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t,
          (K : ℝ) ^ (n + 1) * |s - 0| ^ n / n.factorial * ‖x₀‖ := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        calc
          ‖A s (dysonTerm A x₀ n s)‖ ≤ K * ‖dysonTerm A x₀ n s‖ :=
            (A s).le_of_opNorm_le (hK s) _
          _ ≤ K * ((K * |s|) ^ n / n.factorial * ‖x₀‖) := by
            gcongr
            exact hn s
          _ = (K : ℝ) ^ (n + 1) * |s - 0| ^ n / n.factorial * ‖x₀‖ := by
            rw [sub_zero, mul_pow, pow_succ]
            ring
      _ ≤ (K * |t|) ^ (n + 1) / (n + 1).factorial * ‖x₀‖ := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_norm, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow,
          sub_zero]

theorem dysonTerm_summable (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    Summable (fun n => dysonTerm A x₀ n t) := by
  exact ((Real.summable_pow_div_factorial (K * |t|)).mul_right ‖x₀‖).of_norm_bounded
    (fun n => dysonTerm_norm_le A K hK x₀ n t)

def linearEvolution (A : ℝ → E →L[ℝ] E) (x₀ : E) (t : ℝ) : E :=
  ∑' n, dysonTerm A x₀ n t

theorem linearEvolution_eq_head_add (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    linearEvolution A x₀ t = x₀ + ∑' n, dysonTerm A x₀ (n + 1) t := by
  exact (dysonTerm_summable A K hK x₀ t).tsum_eq_zero_add

theorem linearEvolution_zero (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) :
    linearEvolution A x₀ 0 = x₀ := by
  rw [linearEvolution_eq_head_add A K hK]
  simp only [dysonTerm_succ_zero, tsum_zero, add_zero]

theorem linearEvolution_hasDerivAt (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    HasDerivAt (linearEvolution A x₀) (A t (linearEvolution A x₀ t)) t := by
  let R : ℝ := |t| + 1
  let bound : ℕ → ℝ := fun n => K * ((K * R) ^ n / n.factorial * ‖x₀‖)
  have hb : Summable bound :=
    ((Real.summable_pow_div_factorial (K * R)).mul_right ‖x₀‖).mul_left (K : ℝ)
  have hg : ∀ n s, s ∈ Ioo (-R) R →
      ‖A s (dysonTerm A x₀ n s)‖ ≤ bound n := by
    intro n s hs
    calc
      _ ≤ K * ‖dysonTerm A x₀ n s‖ := (A s).le_of_opNorm_le (hK s) _
      _ ≤ K * ((K * |s|) ^ n / n.factorial * ‖x₀‖) := by
        gcongr
        exact dysonTerm_norm_le A K hK x₀ n s
      _ ≤ bound n := by
        dsimp [bound]
        gcongr
        exact (abs_lt.mpr hs).le
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := by dsimp [R]; constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-R) R := by
    exact abs_lt.mp (lt_add_one |t|)
  have hsum0 : Summable (fun n => dysonTerm A x₀ (n + 1) 0) := by
    simpa only [dysonTerm_succ_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : E)))
  have hd := hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n s _ => dysonTerm_succ_hasDerivAt A hA x₀ n s) hg hzero hsum0 ht
  have hmap : (∑' n, A t (dysonTerm A x₀ n t)) = A t (linearEvolution A x₀ t) :=
    ((A t).map_tsum (dysonTerm_summable A K hK x₀ t)).symm
  rw [hmap] at hd
  have hder := (hasDerivAt_const t x₀).add hd
  simp only [zero_add] at hder
  convert hder using 1
  ext s
  exact linearEvolution_eq_head_add A K hK x₀ s

theorem operatorEvaluation_continuous (A : ℝ → E →L[ℝ] E)
    (hA : ∀ x, Continuous (fun t => A t x))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) :
    Continuous (fun p : ℝ × E => A p.1 p.2) := by
  exact continuous_prod_of_continuous_lipschitzWith' _ K
    (fun t => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t)) hA

theorem exists_global_linear_solution (A : ℝ → E →L[ℝ] E)
    (hA : ∀ x, Continuous (fun t => A t x))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ ∀ t, HasDerivAt u (A t (u t)) t := by
  exact ⟨linearEvolution A x₀, linearEvolution_zero A K hK x₀,
    linearEvolution_hasDerivAt A (operatorEvaluation_continuous A hA K hK) K hK x₀⟩

end NDEAEvolve.Exp014


-- SOURCE lean/WeightedFourier.lean SHA256 dbab1adb7cc5d6c4ccf2bc08b0fafd5ec1bc6f0fcdf5dfb14e61d72bbdffc582

/-! A complete all-mode Fourier state space. Its coordinates store the second
weighted coefficients, so completeness is inherited from Mathlib's ℓ¹ space.
The free Schrödinger flow is an isometry and is jointly continuous in time and
state; operator-norm continuity of the flow is not asserted. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

abbrev FourierState (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℤ => H) 1

def weight (m : ℤ) : ℝ := (1 + |(m : ℝ)|)^2

theorem weight_one_le (m : ℤ) : 1 ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ)]

theorem weight_pos (m : ℤ) : 0 < weight m := lt_of_lt_of_le zero_lt_one (weight_one_le m)

theorem weight_ge_one (m : ℤ) : 1 ≤ weight m := weight_one_le m

theorem abs_frequency_le_weight (m : ℤ) : |(m : ℝ)| ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ), sq_nonneg |(m : ℝ)|]

theorem frequency_sq_le_weight (m : ℤ) : (m : ℝ)^2 ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ), sq_abs (m : ℝ)]

theorem abs_frequency_div_weight_le (m : ℤ) : |(m : ℝ)| / weight m ≤ 1 := by
  exact (div_le_one (weight_pos m)).mpr (abs_frequency_le_weight m)

theorem frequency_sq_div_weight_le (m : ℤ) : (m : ℝ)^2 / weight m ≤ 1 := by
  exact (div_le_one (weight_pos m)).mpr (frequency_sq_le_weight m)

theorem weight_add_le (m n : ℤ) : weight (m+n) ≤ weight m * weight n := by
  have habs : |((m+n : ℤ) : ℝ)| ≤ |(m : ℝ)| + |(n : ℝ)| := by
    simpa using abs_add_le (m : ℝ) (n : ℝ)
  have hbase : 1 + |((m+n : ℤ) : ℝ)| ≤ (1+|(m : ℝ)|)*(1+|(n : ℝ)|) := by
    nlinarith [abs_nonneg (m : ℝ), abs_nonneg (n : ℝ),
      mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg (n : ℝ))]
  unfold weight
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hbase 2

theorem weight_neg (m : ℤ) : weight (-m) = weight m := by simp [weight]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def coefficient (b : FourierState H) (m : ℤ) : H :=
  (((weight m)⁻¹ : ℝ) : ℂ) • b m

def coefficientCLM (m : ℤ) : FourierState H →L[ℂ] H :=
  (((weight m)⁻¹ : ℝ) : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => H) 1 m

theorem coefficientCLM_apply (m : ℤ) (b : FourierState H) :
    coefficientCLM m b = coefficient b m := rfl

omit [NormedSpace ℂ H] in
theorem state_summable_norm (b : FourierState H) : Summable (fun m : ℤ => ‖b m‖) := by
  simpa using (lp.memℓp b).summable (by norm_num : 0 < (1 : ENNReal).toReal)

omit [NormedSpace ℂ H] in
theorem state_tsum_norm (b : FourierState H) : (∑' m : ℤ, ‖b m‖) = ‖b‖ := by
  simpa using (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) b).symm

theorem coefficient_norm (b : FourierState H) (m : ℤ) :
    ‖coefficient b m‖ = (weight m)⁻¹ * ‖b m‖ := by
  simp only [coefficient, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (weight_pos m).le)]

theorem weight_mul_coefficient_norm (b : FourierState H) (m : ℤ) :
    weight m * ‖coefficient b m‖ = ‖b m‖ := by
  rw [coefficient_norm, ← mul_assoc, mul_inv_cancel₀ (weight_pos m).ne', one_mul]

theorem weighted_summable (b : FourierState H) :
    Summable (fun m : ℤ => weight m * ‖coefficient b m‖) := by
  simpa only [weight_mul_coefficient_norm] using state_summable_norm b

theorem weighted_tsum_norm (b : FourierState H) :
    (∑' m : ℤ, weight m * ‖coefficient b m‖) = ‖b‖ := by
  simpa only [weight_mul_coefficient_norm] using state_tsum_norm b

def ofCoefficients (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) : FourierState H :=
  ⟨fun m => (weight m : ℂ) • a m, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (weight_pos _).le] using ha⟩

theorem ofCoefficients_apply (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) (m : ℤ) :
    ofCoefficients a ha m = (weight m : ℂ) • a m := rfl

theorem coefficient_ofCoefficients (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) (m : ℤ) :
    coefficient (ofCoefficients a ha) m = a m := by
  rw [coefficient, ofCoefficients_apply, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (weight_pos m).ne', Complex.ofReal_one, one_smul]

theorem ofCoefficients_norm (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) :
    ‖ofCoefficients a ha‖ = ∑' m : ℤ, weight m * ‖a m‖ := by
  simpa only [coefficient_ofCoefficients] using (weighted_tsum_norm (ofCoefficients a ha)).symm

theorem coefficient_summable_norm (b : FourierState H) :
    Summable (fun m : ℤ => ‖coefficient b m‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (weight_one_le m)
      (norm_nonneg (coefficient b m))) (weighted_summable b)

theorem coefficient_summable [CompleteSpace H] (b : FourierState H) :
    Summable (coefficient b) := (coefficient_summable_norm b).of_norm

def phase (t : ℝ) (m : ℤ) : ℂ := Complex.exp (-Complex.I * (m : ℂ)^2 * (t : ℂ))

theorem phase_norm (t : ℝ) (m : ℤ) : ‖phase t m‖ = 1 := by
  simp [phase, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem phase_zero (m : ℤ) : phase 0 m = 1 := by simp [phase]

theorem phase_add (s t : ℝ) (m : ℤ) : phase (s+t) m = phase s m * phase t m := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phase_continuous (m : ℤ) : Continuous (fun t : ℝ => phase t m) := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem phase_hasDerivAt (t : ℝ) (m : ℤ) :
    HasDerivAt (fun s : ℝ => phase s m) ((-Complex.I*(m : ℂ)^2) * phase t m) t := by
  have hd : HasDerivAt (fun s : ℝ => (-Complex.I*(m : ℂ)^2)*(s : ℂ))
      (-Complex.I*(m : ℂ)^2) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      ((hasDerivAt_id t).ofReal_comp.const_mul (-Complex.I*(m : ℂ)^2))
  simpa only [phase, mul_comm] using! hd.cexp

def freeFlowLinear (t : ℝ) : FourierState H →ₗ[ℂ] FourierState H where
  toFun b := ⟨fun m => phase t m • b m, (lp.memℓp b).mono' (fun m => by
    simp only [norm_smul, phase_norm, one_mul, le_refl])⟩
  map_add' b c := by
    apply lp.ext
    funext m
    exact smul_add (phase t m) (b m) (c m)
  map_smul' c b := by
    apply lp.ext
    funext m
    exact smul_comm (phase t m) c (b m)

theorem freeFlowLinear_apply (t : ℝ) (b : FourierState H) (m : ℤ) :
    freeFlowLinear t b m = phase t m • b m := rfl

theorem freeFlowLinear_norm (t : ℝ) (b : FourierState H) : ‖freeFlowLinear t b‖ = ‖b‖ := by
  rw [← state_tsum_norm, ← state_tsum_norm]
  simp only [freeFlowLinear_apply, norm_smul, phase_norm, one_mul]

def freeFlow (t : ℝ) : FourierState H →L[ℂ] FourierState H :=
  (freeFlowLinear t).mkContinuous 1 (fun b => by simp [freeFlowLinear_norm])

theorem freeFlow_apply (t : ℝ) (b : FourierState H) (m : ℤ) :
    freeFlow t b m = phase t m • b m := rfl

theorem freeFlow_norm (t : ℝ) (b : FourierState H) : ‖freeFlow t b‖ = ‖b‖ :=
  freeFlowLinear_norm t b

theorem freeFlow_opNorm_le (t : ℝ) : ‖freeFlow (H := H) t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun b => by simp [freeFlow_norm])

theorem freeFlow_zero (b : FourierState H) : freeFlow 0 b = b := by
  apply lp.ext
  funext m
  simp only [freeFlow_apply, phase_zero, one_smul]

theorem freeFlow_add (s t : ℝ) (b : FourierState H) :
    freeFlow (s+t) b = freeFlow s (freeFlow t b) := by
  apply lp.ext
  funext m
  simp only [freeFlow_apply, phase_add, smul_smul]

theorem freeFlow_neg_cancel (t : ℝ) (b : FourierState H) :
    freeFlow (-t) (freeFlow t b) = b := by
  rw [← freeFlow_add, neg_add_cancel, freeFlow_zero]

theorem freeFlow_isometry (t : ℝ) : Isometry (freeFlow (H := H) t) := by
  apply isometry_iff_dist_eq.mpr
  intro b c
  rw [dist_eq_norm, ← map_sub, freeFlow_norm, dist_eq_norm]

theorem coefficient_freeFlow (t : ℝ) (b : FourierState H) (m : ℤ) :
    coefficient (freeFlow t b) m = phase t m • coefficient b m := by
  simp only [coefficient, freeFlow_apply]
  exact smul_comm _ _ _

variable [CompleteSpace H]

omit [CompleteSpace H] in
theorem freeFlow_eq_tsum (t : ℝ) (b : FourierState H) :
    freeFlow t b = ∑' m : ℤ, lp.single 1 m (phase t m • b m) := by
  have h := lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤) (freeFlow t b)
  simpa only [freeFlow_apply] using h.tsum_eq.symm

theorem freeFlow_continuous (b : FourierState H) :
    Continuous (fun t : ℝ => freeFlow t b) := by
  have hterm (m : ℤ) : Continuous
      (fun t : ℝ => lp.single (E := fun _ : ℤ => H) 1 m (phase t m • b m)) := by
    have hc : Continuous (fun t : ℝ => phase t m • b m) :=
      (phase_continuous m).smul continuous_const
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => H) 1 m).continuous.comp hc
  have hc := continuous_tsum hterm (state_summable_norm b) (fun m t => by
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_smul, phase_norm, one_mul])
  simpa only [← freeFlow_eq_tsum] using hc

theorem freeFlow_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => freeFlow p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, htime⟩ := Metric.continuousAt_iff.mp
    (freeFlow_continuous p.2).continuousAt (ε/2) (by positivity)
  refine ⟨min δ (ε/2), lt_min hδ (by positivity), ?_⟩
  intro q hq
  change max (dist q.1 p.1) (dist q.2 p.2) < min δ (ε/2) at hq
  have ht : dist q.1 p.1 < δ :=
    (lt_of_le_of_lt (le_max_left _ _) hq).trans_le (min_le_left _ _)
  have hb : dist q.2 p.2 < ε/2 :=
    (lt_of_le_of_lt (le_max_right _ _) hq).trans_le (min_le_right _ _)
  have h := htime ht
  calc
    dist (freeFlow q.1 q.2) (freeFlow p.1 p.2) ≤
        dist (freeFlow q.1 q.2) (freeFlow q.1 p.2) +
          dist (freeFlow q.1 p.2) (freeFlow p.1 p.2) := dist_triangle _ _ _
    _ = dist q.2 p.2 + dist (freeFlow q.1 p.2) (freeFlow p.1 p.2) := by
      rw [(freeFlow_isometry q.1).dist_eq]
    _ < ε := by linarith

end NDEAEvolve.Exp014


-- SOURCE lean/ScalarSeries.lean SHA256 ccf216c8e343a9d0b1b213539c8c56c23bad763257ebf5b1d9458cf32faa38e6

/-! Bounded scalar Fourier multipliers followed by summation. Strong joint
continuity and derivatives are derived from ℓ¹ summability of each fixed input.
No summable supremum over a compact family of inputs is assumed. -/
noncomputable section
open scoped BigOperators Topology NNReal
namespace NDEAEvolve.Exp014

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

def scalarSeries (c : ℤ → ℂ) (b : lp (fun _ : ℤ => H) 1) : H :=
  ∑' m, c m • b m

theorem scalarSeries_summable (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : Summable (fun m => c m • b m) := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  apply hb.of_norm_bounded
  intro m
  simpa only [norm_smul, one_mul] using
    mul_le_mul_of_nonneg_right (hc m) (norm_nonneg (b m))

private theorem scalar_identity_norm_le (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c • ContinuousLinearMap.id ℂ H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖c • x‖ ≤ 1 * ‖x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg x)

def scalarSeriesCLM (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    lp (fun _ : ℤ => H) 1 →L[ℂ] H :=
  (lp.tsumCLM (𝕜 := ℂ) (α := ℤ) (E := H)).comp
    (lp.mapCLM 1 (fun m => c m • ContinuousLinearMap.id ℂ H) zero_le_one
      (fun m => scalar_identity_norm_le (c m) (hc m)))

theorem scalarSeriesCLM_apply (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : scalarSeriesCLM c hc b = scalarSeries c b := rfl

theorem scalarSeriesCLM_norm_le (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    ‖scalarSeriesCLM (H := H) c hc‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have h1 : ‖lp.tsumCLM (𝕜 := ℂ) (α := ℤ) (E := H)‖ ≤ 1 := lp.norm_tsumCLM_le
  have h2 := lp.norm_mapCLM_le 1 (fun m : ℤ => c m • ContinuousLinearMap.id ℂ H)
    zero_le_one (fun m => scalar_identity_norm_le (c m) (hc m))
  simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one

theorem scalarSeries_norm_le (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : ‖scalarSeries c b‖ ≤ ‖b‖ := by
  change ‖scalarSeriesCLM c hc b‖ ≤ ‖b‖
  simpa only [one_mul] using
    (scalarSeriesCLM (H := H) c hc).le_of_opNorm_le
      (scalarSeriesCLM_norm_le (H := H) c hc) b

theorem scalarSeries_continuous {P : Type*} [TopologicalSpace P]
    (c : P → ℤ → ℂ) (hc : ∀ p m, ‖c p m‖ ≤ 1)
    (hcont : ∀ m, Continuous (fun p => c p m)) (b : lp (fun _ : ℤ => H) 1) :
    Continuous (fun p => scalarSeries (c p) b) := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  exact continuous_tsum (fun m => (hcont m).smul continuous_const) hb
    (fun m p => by simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (hc p m) (norm_nonneg (b m)))

theorem scalarSeries_joint_continuous {P : Type*} [TopologicalSpace P]
    (c : P → ℤ → ℂ) (hc : ∀ p m, ‖c p m‖ ≤ 1)
    (hcont : ∀ m, Continuous (fun p => c p m)) :
    Continuous (fun q : P × lp (fun _ : ℤ => H) 1 => scalarSeries (c q.1) q.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro p
    change LipschitzWith 1 (scalarSeriesCLM (H := H) (c p) (hc p))
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := (1 : ℝ≥0))
      (scalarSeriesCLM_norm_le (H := H) (c p) (hc p))
  · exact scalarSeries_continuous c hc hcont

theorem scalarSeries_hasDerivAt (c c' : ℝ → ℤ → ℂ)
    (hc : ∀ t m, ‖c t m‖ ≤ 1) (hc' : ∀ t m, ‖c' t m‖ ≤ 1)
    (hd : ∀ t m, HasDerivAt (fun s => c s m) (c' t m) t)
    (b : lp (fun _ : ℤ => H) 1) (t : ℝ) :
    HasDerivAt (fun s => scalarSeries (c s) b) (scalarSeries (c' t) b) t := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  exact hasDerivAt_tsum hb (fun m s => (hd s m).smul_const (b m))
    (fun m s => by simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (hc' s m) (norm_nonneg (b m)))
    (scalarSeries_summable (c 0) (hc 0) b) t

end NDEAEvolve.Exp014


-- SOURCE lean/FourierPotential.lean SHA256 2fbcce8942ec08dd641792c399c85efccb6575c22544b3cb1f669df8ae9c803e

/-! Regular operator-valued Fourier potentials act by a bounded convolution
on the complete second-moment coefficient space. Each shift is constructed
before taking the operator-norm convergent infinite sum. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

private theorem operatorSeries_summable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℤ → E →L[ℂ] F) (g : ℤ → ℝ) (hg : Summable g)
    (hfg : ∀ j, ‖f j‖ ≤ g j) : Summable f :=
  hg.of_norm_bounded hfg

private theorem operatorSeries_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℤ → E →L[ℂ] F) (g : ℤ → ℝ) (hg : Summable g)
    (hfg : ∀ j, ‖f j‖ ≤ g j) : ‖∑' j, f j‖ ≤ ∑' j, g j :=
  tsum_of_norm_bounded hg.hasSum hfg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RegularPotential (v : ℤ → H →L[ℂ] H) : Prop :=
  Summable fun j => weight j * ‖v j‖

def HermitianFourierPotential (v : ℤ → H →L[ℂ] H) : Prop :=
  ∀ j, v (-j) = star (v j)

def character (x : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))

theorem character_norm (x : ℝ) (m : ℤ) : ‖character x m‖ = 1 := by
  simp [character, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem character_continuous (m : ℤ) : Continuous (fun x => character x m) := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem character_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y => character y m) ((Complex.I * (m : ℂ)) * character x m) x := by
  simpa [character, mul_comm] using!
    (((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * (m : ℂ))).cexp).comp_ofReal

theorem character_periodic (m : ℤ) :
    Function.Periodic (fun x => character x m) (2 * Real.pi) := by
  intro x
  have he : Complex.I * (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  simp only [character, Complex.ofReal_add, mul_add, Complex.exp_add, he,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem character_add (x : ℝ) (j m : ℤ) :
    character x (j + m) = character x j * character x m := by
  simp only [character, Int.cast_add, mul_add, add_mul, Complex.exp_add]

theorem character_star (x : ℝ) (j : ℤ) :
    star (character x j) = character x (-j) := by
  simp only [character, RCLike.star_def, ← Complex.exp_conj, map_mul,
    map_intCast, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
  congr 1
  ring

theorem potential_weight_add_le (j m : ℤ) :
    weight (j + m) ≤ weight j * weight m := weight_add_le j m

theorem potential_weight_ratio_le (j m : ℤ) :
    weight m / weight (m - j) ≤ weight j := by
  apply (div_le_iff₀ (weight_pos (m - j))).mpr
  have he : j + (m - j) = m := by omega
  simpa only [he] using potential_weight_add_le j (m - j)

private def subtractEquiv (j : ℤ) : ℤ ≃ ℤ where
  toFun m := m - j
  invFun m := m + j
  left_inv m := sub_add_cancel m j
  right_inv m := add_sub_cancel_right m j

private theorem state_norm_eq (b : FourierState H) : ‖b‖ = ∑' m, ‖b m‖ := by
  exact (state_tsum_norm b).symm

private def shiftValue (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) (m : ℤ) : H :=
  ((weight m / weight (m - j) : ℝ) : ℂ) • A (b (m - j))

private theorem shiftValue_norm_le (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (m : ℤ) :
    ‖shiftValue j A b m‖ ≤ (weight j * ‖A‖) * ‖b (m - j)‖ := by
  have hr : 0 ≤ weight m / weight (m - j) :=
    div_nonneg (weight_pos m).le (weight_pos (m - j)).le
  rw [shiftValue, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  calc
    _ ≤ (weight m / weight (m - j)) * (‖A‖ * ‖b (m - j)‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) hr
    _ ≤ weight j * (‖A‖ * ‖b (m - j)‖) :=
      mul_le_mul_of_nonneg_right (potential_weight_ratio_le j m) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

private theorem shiftValue_summable_norm (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) : Summable fun m => ‖shiftValue j A b m‖ := by
  have hs : Summable fun m => ‖b (m - j)‖ :=
    (subtractEquiv j).summable_iff.mpr (state_summable_norm b)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (shiftValue_norm_le j A b) (hs.mul_left (weight j * ‖A‖))

private def shiftState (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) : FourierState H :=
  ⟨shiftValue j A b, memℓp_gen (by simpa using shiftValue_summable_norm j A b)⟩

private theorem shiftState_norm_le (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) :
    ‖shiftState j A b‖ ≤ (weight j * ‖A‖) * ‖b‖ := by
  rw [state_norm_eq]
  change (∑' m, ‖shiftValue j A b m‖) ≤ _
  have hs : Summable fun m => ‖b (m - j)‖ :=
    (subtractEquiv j).summable_iff.mpr (state_summable_norm b)
  calc
    _ ≤ ∑' m, (weight j * ‖A‖) * ‖b (m - j)‖ :=
      (shiftValue_summable_norm j A b).tsum_le_tsum (shiftValue_norm_le j A b)
        (hs.mul_left _)
    _ = (weight j * ‖A‖) * ∑' m, ‖b m‖ := by
      rw [tsum_mul_left]
      exact congrArg (fun r : ℝ => (weight j * ‖A‖) * r)
        ((subtractEquiv j).tsum_eq (fun m => ‖b m‖))
    _ = _ := by rw [← state_norm_eq]

def potentialShift (j : ℤ) (A : H →L[ℂ] H) : FourierState H →L[ℂ] FourierState H :=
  LinearMap.mkContinuous
    { toFun := shiftState j A
      map_add' := by
        intro b c
        apply lp.ext
        funext m
        simp [shiftState, shiftValue, map_add, smul_add]
      map_smul' := by
        intro z b
        apply lp.ext
        funext m
        simp [shiftState, shiftValue, map_smul, smul_smul, mul_comm] }
    (weight j * ‖A‖) (shiftState_norm_le j A)

theorem potentialShift_apply (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) (m : ℤ) :
    potentialShift j A b m = ((weight m / weight (m - j) : ℝ) : ℂ) • A (b (m - j)) := rfl

theorem potentialShift_norm_le (j : ℤ) (A : H →L[ℂ] H) :
    ‖potentialShift j A‖ ≤ weight j * ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (weight_pos j).le (norm_nonneg A))
  exact shiftState_norm_le j A

theorem coefficient_potentialShift (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (m : ℤ) :
    coefficient (potentialShift j A b) m = A (coefficient b (m - j)) := by
  simp only [coefficient, potentialShift_apply, map_smul, smul_smul]
  congr 1
  have hm : (weight m : ℂ) ≠ 0 := by exact_mod_cast (weight_pos m).ne'
  have hj : (weight (m - j) : ℂ) ≠ 0 := by exact_mod_cast (weight_pos (m - j)).ne'
  push_cast
  field_simp [hm, hj]

def potentialConvolution (v : ℤ → H →L[ℂ] H) : FourierState H →L[ℂ] FourierState H :=
  ∑' j, potentialShift j (v j)

theorem potentialShift_summable_norm (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => ‖potentialShift j (v j)‖ := by
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg (potentialShift j (v j)))
    (fun j => potentialShift_norm_le j (v j)) hv

theorem potentialShift_summable (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => potentialShift j (v j) := by
  exact operatorSeries_summable (fun j => potentialShift j (v j))
    (fun j => weight j * ‖v j‖) hv (fun j => potentialShift_norm_le j (v j))

theorem potentialConvolution_norm_le (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    ‖potentialConvolution v‖ ≤ ∑' j, weight j * ‖v j‖ := by
  change ‖∑' j, potentialShift j (v j)‖ ≤ _
  exact operatorSeries_norm_le (fun j => potentialShift j (v j))
    (fun j => weight j * ‖v j‖) hv (fun j => potentialShift_norm_le j (v j))

theorem potentialConvolution_apply (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b : FourierState H) :
    potentialConvolution v b = ∑' j, potentialShift j (v j) b := by
  exact (ContinuousLinearMap.apply ℂ (FourierState H) b).map_tsum (potentialShift_summable v hv)

theorem coefficient_potentialConvolution (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b : FourierState H) (m : ℤ) :
    coefficient (potentialConvolution v b) m = ∑' j, v j (coefficient b (m - j)) := by
  rw [potentialConvolution_apply v hv]
  have hs : Summable (fun j => potentialShift j (v j) b) :=
    (potentialShift_summable v hv).mapL (ContinuousLinearMap.apply ℂ (FourierState H) b)
  change coefficientCLM m (∑' j, potentialShift j (v j) b) = _
  exact ((coefficientCLM m).map_tsum hs).trans
    (tsum_congr fun j => coefficient_potentialShift j (v j) b m)

def operatorPotential (v : ℤ → H →L[ℂ] H) (x : ℝ) : H →L[ℂ] H :=
  ∑' j, character x j • v j

theorem regularPotential_absolute (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => ‖v j‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hv
  intro j
  exact le_mul_of_one_le_left (norm_nonneg _) (weight_one_le j)

theorem operatorPotential_summable_norm (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (x : ℝ) :
    Summable fun j => ‖character x j • v j‖ := by
  simpa only [norm_smul, character_norm, one_mul] using regularPotential_absolute v hv

theorem operatorPotential_apply (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (x : ℝ) (y : H) :
    operatorPotential v x y = ∑' j, character x j • v j y := by
  exact (ContinuousLinearMap.apply ℂ H y).map_tsum
    (operatorPotential_summable_norm v hv x).of_norm

theorem operatorPotential_norm_le (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (x : ℝ) : ‖operatorPotential v x‖ ≤ ∑' j, ‖v j‖ := by
  unfold operatorPotential
  simpa only [norm_smul, character_norm, one_mul] using
    norm_tsum_le_tsum_norm (operatorPotential_summable_norm v hv x)

theorem operatorPotential_periodic (v : ℤ → H →L[ℂ] H) :
    Function.Periodic (operatorPotential v) (2 * Real.pi) := by
  intro x
  unfold operatorPotential
  apply tsum_congr
  intro j
  exact congrArg (fun z : ℂ => z • v j) (character_periodic j x)

theorem operatorPotential_continuous (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) : Continuous (operatorPotential v) := by
  exact continuous_tsum (fun j => (character_continuous j).smul continuous_const)
    (regularPotential_absolute v hv) (fun j x => by simp [norm_smul, character_norm])

theorem operatorPotential_selfAdjoint (v : ℤ → H →L[ℂ] H)
    (hv : HermitianFourierPotential v) (x : ℝ) : IsSelfAdjoint (operatorPotential v x) := by
  change star (operatorPotential v x) = operatorPotential v x
  rw [operatorPotential, tsum_star]
  calc
    (∑' j, star (character x j • v j)) = ∑' j, character x (-j) • v (-j) := by
      apply tsum_congr
      intro j
      rw [star_smul, character_star, ← hv j]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun j => character x j • v j)

end NDEAEvolve.Exp014


-- SOURCE lean/FourierSynthesis.lean SHA256 52a0f4e618b309caa96a0f8d9af9133498d4040cc5f8fd95aeab557874855e88

/-! Synthesis and the actual spatial derivatives from the second-moment
Fourier state. All three evaluation maps are bounded, hence support joint
continuity along continuous state curves. -/
noncomputable section
open scoped BigOperators Topology
namespace NDEAEvolve.Exp014

def synthesisMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  character x m * ((weight m : ℂ)⁻¹)

def firstMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  (Complex.I * (m : ℂ)) * synthesisMultiplier x m

def secondMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  (-(m : ℂ)^2) * synthesisMultiplier x m

theorem synthesisMultiplier_norm (x : ℝ) (m : ℤ) :
    ‖synthesisMultiplier x m‖ = (weight m)⁻¹ := by
  simp [synthesisMultiplier, character_norm, Complex.norm_real,
    Real.norm_eq_abs, (weight_pos m).le]

theorem synthesisMultiplier_bound (x : ℝ) (m : ℤ) :
    ‖synthesisMultiplier x m‖ ≤ 1 := by
  rw [synthesisMultiplier_norm]
  exact (inv_le_one₀ (weight_pos m)).mpr (weight_one_le m)

theorem firstMultiplier_bound (x : ℝ) (m : ℤ) : ‖firstMultiplier x m‖ ≤ 1 := by
  simpa [firstMultiplier, norm_mul, Complex.norm_intCast,
    synthesisMultiplier_norm, div_eq_mul_inv] using abs_frequency_div_weight_le m

theorem secondMultiplier_bound (x : ℝ) (m : ℤ) : ‖secondMultiplier x m‖ ≤ 1 := by
  simpa [secondMultiplier, norm_mul, norm_neg, norm_pow, Complex.norm_intCast,
    synthesisMultiplier_norm, sq_abs, div_eq_mul_inv] using frequency_sq_div_weight_le m

theorem synthesisMultiplier_continuous (m : ℤ) :
    Continuous (fun x => synthesisMultiplier x m) :=
  (character_continuous m).mul_const _

theorem firstMultiplier_continuous (m : ℤ) : Continuous (fun x => firstMultiplier x m) :=
  (synthesisMultiplier_continuous m).const_mul _

theorem secondMultiplier_continuous (m : ℤ) : Continuous (fun x => secondMultiplier x m) :=
  (synthesisMultiplier_continuous m).const_mul _

theorem synthesisMultiplier_hasDerivAt (x : ℝ) (m : ℤ) :
    HasDerivAt (fun y => synthesisMultiplier y m) (firstMultiplier x m) x := by
  simpa [synthesisMultiplier, firstMultiplier, mul_assoc] using
    (character_hasDerivAt m x).mul_const ((weight m : ℂ)⁻¹)

theorem firstMultiplier_hasDerivAt (x : ℝ) (m : ℤ) :
    HasDerivAt (fun y => firstMultiplier y m) (secondMultiplier x m) x := by
  have h := (synthesisMultiplier_hasDerivAt x m).const_mul (Complex.I * (m : ℂ))
  have he : (Complex.I * (m : ℂ)) * firstMultiplier x m = secondMultiplier x m := by
    simp only [firstMultiplier, secondMultiplier]
    calc
      _ = Complex.I^2 * (m : ℂ)^2 * synthesisMultiplier x m := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [he] at h
  exact h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def synthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (synthesisMultiplier x) (synthesisMultiplier_bound x)

def firstSynthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (firstMultiplier x) (firstMultiplier_bound x)

def secondSynthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (secondMultiplier x) (secondMultiplier_bound x)

def synth (b : FourierState H) (x : ℝ) : H := synthesisCLM x b

def synthFirst (b : FourierState H) (x : ℝ) : H := firstSynthesisCLM x b

def synthSecond (b : FourierState H) (x : ℝ) : H := secondSynthesisCLM x b

theorem synth_eq_tsum (b : FourierState H) (x : ℝ) :
    synth b x = ∑' m, character x m • coefficient b m := by
  change (∑' m, synthesisMultiplier x m • b m) = _
  apply tsum_congr
  intro m
  simp [synthesisMultiplier, coefficient, smul_smul]

theorem synth_norm_le (b : FourierState H) (x : ℝ) : ‖synth b x‖ ≤ ‖b‖ :=
  scalarSeries_norm_le (synthesisMultiplier x) (synthesisMultiplier_bound x) b

theorem synth_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synth p.2 p.1) :=
  scalarSeries_joint_continuous synthesisMultiplier synthesisMultiplier_bound
    synthesisMultiplier_continuous

theorem synthFirst_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synthFirst p.2 p.1) :=
  scalarSeries_joint_continuous firstMultiplier firstMultiplier_bound firstMultiplier_continuous

theorem synthSecond_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synthSecond p.2 p.1) :=
  scalarSeries_joint_continuous secondMultiplier secondMultiplier_bound secondMultiplier_continuous

theorem synth_hasDerivAt (b : FourierState H) (x : ℝ) :
    HasDerivAt (synth b) (synthFirst b x) x :=
  scalarSeries_hasDerivAt synthesisMultiplier firstMultiplier synthesisMultiplier_bound
    firstMultiplier_bound synthesisMultiplier_hasDerivAt b x

theorem synthFirst_hasDerivAt (b : FourierState H) (x : ℝ) :
    HasDerivAt (synthFirst b) (synthSecond b x) x :=
  scalarSeries_hasDerivAt firstMultiplier secondMultiplier firstMultiplier_bound
    secondMultiplier_bound firstMultiplier_hasDerivAt b x

theorem synth_periodic (b : FourierState H) : Function.Periodic (synth b) (2 * Real.pi) := by
  intro x
  simp only [synth_eq_tsum]
  apply tsum_congr
  intro m
  have hp : character (x + 2 * Real.pi) m = character x m := character_periodic m x
  rw [hp]

def freeMultiplier (t x : ℝ) (m : ℤ) : ℂ := phase t m * synthesisMultiplier x m

def freeDerivativeMultiplier (t x : ℝ) (m : ℤ) : ℂ :=
  Complex.I * (phase t m * secondMultiplier x m)

theorem freeMultiplier_bound (t x : ℝ) (m : ℤ) : ‖freeMultiplier t x m‖ ≤ 1 := by
  simpa [freeMultiplier, norm_mul, phase_norm] using synthesisMultiplier_bound x m

theorem freeDerivativeMultiplier_bound (t x : ℝ) (m : ℤ) :
    ‖freeDerivativeMultiplier t x m‖ ≤ 1 := by
  simpa [freeDerivativeMultiplier, norm_mul, phase_norm] using secondMultiplier_bound x m

theorem freeMultiplier_hasDerivAt (t x : ℝ) (m : ℤ) :
    HasDerivAt (fun s => freeMultiplier s x m) (freeDerivativeMultiplier t x m) t := by
  have h := (phase_hasDerivAt t m).mul_const (synthesisMultiplier x m)
  have he : ((-Complex.I * (m : ℂ)^2) * phase t m) * synthesisMultiplier x m =
      freeDerivativeMultiplier t x m := by
    simp only [freeDerivativeMultiplier, secondMultiplier]
    ring
  rw [he] at h
  exact h

theorem freeMultiplier_series (b : FourierState H) (t x : ℝ) :
    scalarSeries (freeMultiplier t x) b = synth (freeFlow t b) x := by
  change (∑' m, freeMultiplier t x m • b m) =
    ∑' m, synthesisMultiplier x m • freeFlow t b m
  apply tsum_congr
  intro m
  simp [freeMultiplier, freeFlow_apply, smul_smul, mul_comm]

theorem freeDerivativeMultiplier_series (b : FourierState H) (t x : ℝ) :
    scalarSeries (freeDerivativeMultiplier t x) b = Complex.I • synthSecond (freeFlow t b) x := by
  rw [scalarSeries]
  change (∑' m, freeDerivativeMultiplier t x m • b m) =
    Complex.I • ∑' m, secondMultiplier x m • freeFlow t b m
  rw [← (scalarSeries_summable (secondMultiplier x) (secondMultiplier_bound x) (freeFlow t b)).tsum_const_smul]
  apply tsum_congr
  intro m
  simp [freeDerivativeMultiplier, freeFlow_apply, smul_smul, mul_comm]

theorem synth_freeFlow_hasDerivAt (b : FourierState H) (t x : ℝ) :
    HasDerivAt (fun s => synth (freeFlow s b) x)
      (Complex.I • synthSecond (freeFlow t b) x) t := by
  have h := scalarSeries_hasDerivAt (fun s => freeMultiplier s x)
    (fun s => freeDerivativeMultiplier s x)
    (fun s => freeMultiplier_bound s x) (fun s => freeDerivativeMultiplier_bound s x)
    (fun s => freeMultiplier_hasDerivAt s x) b t
  simpa only [freeMultiplier_series, freeDerivativeMultiplier_series] using h

end NDEAEvolve.Exp014


-- SOURCE lean/FourierProduct.lean SHA256 b2045efcd619f1c588fe047608e7b11e822b70ea584a3038b6c0843ae1c473f4

/-! Fourier synthesis identifies the bounded coefficient convolution with
actual pointwise multiplication by the synthesized spatial potential. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def translateEquiv (j : ℤ) : ℤ ≃ ℤ where
  toFun m := m + j
  invFun m := m - j
  left_inv m := add_sub_cancel_right m j
  right_inv m := sub_add_cancel m j

theorem synthesis_terms_summable (b : FourierState H) (x : ℝ) :
    Summable fun m => character x m • coefficient b m := by
  apply Summable.of_norm
  simpa only [norm_smul, character_norm, one_mul] using coefficient_summable_norm b

theorem synth_potentialShift (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (x : ℝ) :
    synth (potentialShift j A b) x = character x j • A (synth b x) := by
  calc
    _ = ∑' m, character x m • A (coefficient b (m - j)) := by
      simp only [synth_eq_tsum, coefficient_potentialShift]
    _ = ∑' m, character x (m + j) • A (coefficient b m) := by
      simpa only [translateEquiv, Equiv.coe_fn_mk, add_sub_cancel_right] using
        ((translateEquiv j).tsum_eq
          (fun m => character x m • A (coefficient b (m - j)))).symm
    _ = character x j • A (synth b x) := by
      rw [synth_eq_tsum, A.map_tsum (synthesis_terms_summable b x),
        ← ((synthesis_terms_summable b x).mapL A).tsum_const_smul (character x j)]
      apply tsum_congr
      intro m
      simp only [character_add, map_smul, smul_smul, mul_comm]

theorem synth_potentialConvolution (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (b : FourierState H) (x : ℝ) :
    synth (potentialConvolution v b) x = operatorPotential v x (synth b x) := by
  have hs : Summable (fun j => potentialShift j (v j) b) :=
    (potentialShift_summable v hv).mapL (ContinuousLinearMap.apply ℂ (FourierState H) b)
  change synthesisCLM x (potentialConvolution v b) = _
  rw [potentialConvolution_apply v hv, (synthesisCLM x).map_tsum hs]
  change (∑' j, synth (potentialShift j (v j) b) x) = _
  simp only [synth_potentialShift]
  exact (operatorPotential_apply v hv x (synth b x)).symm

end NDEAEvolve.Exp014


-- SOURCE lean/ClassicalExistence.lean SHA256 74086199b1de9959d61a09d0ab8f4ae4299d683e135fc2e0a3a062b74c574a41

/-! Global existence of the actual classical periodic PDE from regular Fourier
data and a regular spatially varying potential. The trajectory is constructed
by the Dyson evolution in the interaction picture; the classical PDE is then
derived from bounded synthesis and actual differentiation. -/
noncomputable section
open scoped BigOperators Topology
namespace NDEAEvolve.Exp014

private theorem synthesis_along_continuous_state
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (S : E → ℝ → F) (hS : Continuous (fun p : ℝ × E => S p.2 p.1))
    (q : ℝ → E) (hq : Continuous q) :
    Continuous (fun p : ℝ × ℝ => S (q p.1) p.2) :=
  hS.comp (continuous_snd.prodMk (hq.comp continuous_fst))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def interactionGenerator (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    FourierState H →L[ℂ] FourierState H :=
  (-Complex.I) • (freeFlow (-t)).comp ((potentialConvolution v).comp (freeFlow t))

theorem interactionGenerator_apply (v : ℤ → H →L[ℂ] H) (t : ℝ) (b : FourierState H) :
    interactionGenerator v t b =
      (-Complex.I) • freeFlow (-t) (potentialConvolution v (freeFlow t b)) := rfl

theorem interactionGenerator_bound (v : ℤ → H →L[ℂ] H) (t : ℝ) (b : FourierState H) :
    ‖interactionGenerator v t b‖ ≤ ‖potentialConvolution v‖ * ‖b‖ := by
  rw [interactionGenerator_apply, norm_smul, norm_neg, Complex.norm_I, one_mul, freeFlow_norm]
  simpa only [freeFlow_norm] using (potentialConvolution v).le_opNorm (freeFlow t b)

theorem interactionGenerator_joint_continuous (v : ℤ → H →L[ℂ] H) :
    Continuous (fun p : ℝ × FourierState H => interactionGenerator v p.1 p.2) := by
  have hc := (potentialConvolution v).continuous.comp freeFlow_joint_continuous
  exact (freeFlow_joint_continuous.comp (continuous_fst.neg.prodMk hc)).const_smul (-Complex.I)

def interactionReal (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    FourierState H →L[ℝ] FourierState H := (interactionGenerator v t).restrictScalars ℝ

theorem interactionReal_norm_le (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    ‖interactionReal v t‖ ≤ ‖potentialConvolution v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (potentialConvolution v).opNorm_nonneg
    (interactionGenerator_bound v t)

def interactingState (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) : ℝ → FourierState H :=
  linearEvolution (interactionReal v) b₀

theorem interactingState_zero (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    interactingState v b₀ 0 = b₀ :=
  linearEvolution_zero (interactionReal v) ‖potentialConvolution v‖₊
    (interactionReal_norm_le v) b₀

theorem interactingState_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t : ℝ) :
    HasDerivAt (interactingState v b₀)
      (interactionGenerator v t (interactingState v b₀ t)) t :=
  linearEvolution_hasDerivAt (interactionReal v) (interactionGenerator_joint_continuous v)
    ‖potentialConvolution v‖₊ (interactionReal_norm_le v) b₀ t

theorem interactingState_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (interactingState v b₀) :=
  continuous_iff_continuousAt.mpr fun t => (interactingState_hasDerivAt v b₀ t).continuousAt

def physicalState (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t : ℝ) : FourierState H :=
  freeFlow t (interactingState v b₀ t)

theorem physicalState_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (physicalState v b₀) :=
  freeFlow_joint_continuous.comp (continuous_id.prodMk (interactingState_continuous v b₀))

def solution (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) : H :=
  synth (physicalState v b₀ t) x

theorem solution_zero (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (x : ℝ) :
    solution v b₀ 0 x = synth b₀ x := by
  simp [solution, physicalState, interactingState_zero, freeFlow_zero]

theorem solution_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (fun p : ℝ × ℝ => solution v b₀ p.1 p.2) :=
  synthesis_along_continuous_state (synth (H := H)) (synth_joint_continuous (H := H))
    (physicalState v b₀) (physicalState_continuous v b₀)

theorem solution_space_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (solution v b₀ t) (synthFirst (physicalState v b₀ t) x) x :=
  synth_hasDerivAt (physicalState v b₀ t) x

theorem solution_second_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (deriv (solution v b₀ t)) (synthSecond (physicalState v b₀ t) x) x := by
  have h : deriv (solution v b₀ t) = synthFirst (physicalState v b₀ t) :=
    funext fun y => (solution_space_hasDerivAt v b₀ t y).deriv
  rw [h]
  exact synthFirst_hasDerivAt (physicalState v b₀ t) x

theorem solution_time_hasDerivAt (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (fun s => solution v b₀ s x)
      (Complex.I • synthSecond (physicalState v b₀ t) x +
        (-Complex.I) • operatorPotential v x (solution v b₀ t x)) t := by
  let A : ℝ → FourierState H →L[ℝ] H :=
    fun s => ((synthesisCLM x).comp (freeFlow s)).restrictScalars ℝ
  have hA : Continuous (fun p : ℝ × FourierState H => A p.1 p.2) :=
    (synthesisCLM x).continuous.comp freeFlow_joint_continuous
  have h := strong_apply_hasDerivAt A hA (interactingState v b₀)
    (interactionGenerator v t (interactingState v b₀ t))
    (Complex.I • synthSecond (physicalState v b₀ t) x) t
    (interactingState_hasDerivAt v b₀ t)
    (synth_freeFlow_hasDerivAt (interactingState v b₀ t) t x)
  have he : A t (interactionGenerator v t (interactingState v b₀ t)) =
      (-Complex.I) • operatorPotential v x (solution v b₀ t x) := by
    change synth (freeFlow t ((-Complex.I) • freeFlow (-t)
      (potentialConvolution v (freeFlow t (interactingState v b₀ t))))) x = _
    rw [map_smul, ← freeFlow_add, add_neg_cancel, freeFlow_zero]
    change synthesisCLM x ((-Complex.I) • potentialConvolution v (physicalState v b₀ t)) = _
    rw [map_smul]
    exact congrArg ((-Complex.I) • ·) (synth_potentialConvolution v hv (physicalState v b₀ t) x)
  rw [he] at h
  have hfun : (fun s => A s (interactingState v b₀ s)) =
      (fun s => solution v b₀ s x) := by
    funext s
    rfl
  rw [hfun, add_comm] at h
  exact h

theorem solution_classical (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b₀ : FourierState H) :
    Exp013.IsClassicalPeriodicSolution (2 * Real.pi) (fun _ x => operatorPotential v x)
      0 (solution v b₀) where
  time_differentiable t x := (solution_time_hasDerivAt v hv b₀ t x).differentiableAt
  space_differentiable t x := (solution_space_hasDerivAt v b₀ t x).differentiableAt
  second_space_differentiable t x := (solution_second_hasDerivAt v b₀ t x).differentiableAt
  continuous_solution := solution_continuous v b₀
  continuous_time_derivative := by
    have hsecond : Continuous (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthSecond (H := H)) (synthSecond_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have hvu : Continuous (fun p : ℝ × ℝ =>
        operatorPotential v p.2 (solution v b₀ p.1 p.2)) :=
      ((operatorPotential_continuous v hv).comp continuous_snd).clm_apply
        (solution_continuous v b₀)
    have h := (hsecond.const_smul Complex.I).add (hvu.const_smul (-Complex.I))
    have he : (fun p : ℝ × ℝ => deriv (fun s => solution v b₀ s p.2) p.1) =
        (fun p : ℝ × ℝ => Complex.I • synthSecond (physicalState v b₀ p.1) p.2 +
          (-Complex.I) • operatorPotential v p.2 (solution v b₀ p.1 p.2)) :=
      funext fun p => (solution_time_hasDerivAt v hv b₀ p.1 p.2).deriv
    rw [he]
    exact h
  continuous_space_derivative := by
    have h : Continuous (fun p : ℝ × ℝ => synthFirst (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthFirst (H := H)) (synthFirst_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have he : (fun p : ℝ × ℝ => deriv (solution v b₀ p.1) p.2) =
        (fun p : ℝ × ℝ => synthFirst (physicalState v b₀ p.1) p.2) :=
      funext fun p => (solution_space_hasDerivAt v b₀ p.1 p.2).deriv
    rw [he]
    exact h
  continuous_second_derivative := by
    have h : Continuous (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthSecond (H := H)) (synthSecond_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have he : (fun p : ℝ × ℝ => deriv (deriv (solution v b₀ p.1)) p.2) =
        (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      funext fun p => (solution_second_hasDerivAt v b₀ p.1 p.2).deriv
    rw [he]
    exact h
  periodic t := synth_periodic (physicalState v b₀ t)
  schrodinger t x := by
    rw [(solution_time_hasDerivAt v hv b₀ t x).deriv,
      (solution_second_hasDerivAt v b₀ t x).deriv]
    simp only [Pi.zero_apply, add_zero, smul_add, smul_smul, mul_neg,
      Complex.I_mul_I, neg_neg, neg_one_smul, one_smul]

theorem global_classical_exists_unique (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (hHerm : HermitianFourierPotential v)
    (a : ℤ → H) (ha : Summable (fun m => weight m * ‖a m‖)) :
    ∃! u : ℝ → ℝ → H,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi) (fun _ x => operatorPotential v x) 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • a m := by
  let b₀ := ofCoefficients a ha
  have hi : ∀ x, solution v b₀ 0 x = ∑' m, character x m • a m := by
    intro x
    rw [solution_zero, synth_eq_tsum]
    simp only [b₀, coefficient_ofCoefficients]
  refine ⟨solution v b₀, ⟨solution_classical v hv b₀, hi⟩, ?_⟩
  intro u hu
  apply Exp013.classical_unique (by positivity : 0 < 2 * Real.pi) u (solution v b₀)
    hu.1 (solution_classical v hv b₀) (fun _ x => operatorPotential_selfAdjoint v hHerm x)
  intro x
  exact (hu.2 x).trans (hi x).symm

end NDEAEvolve.Exp014


-- SOURCE lean/Controls.lean SHA256 fff6851ac9d90257c1bb39dba6183854c87e2c2e522d7f82262da952ef48c96c

/-! Exact nonvacuity checks for the all-mode existence theorem. A potential
with two nonzero Fourier coefficients is spatially nonconstant. Initial data
include a signed single mode and a regular family nonzero at every integer.
These controls instantiate the constructed PDE solution, not a truncation. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014.Controls

def singleData (j m : ℤ) : ℂ := if m = j then 1 else 0

theorem singleData_regular (j : ℤ) :
    Summable (fun m : ℤ => weight m * ‖singleData j m‖) := by
  have he : (fun m : ℤ => weight m * ‖singleData j m‖) =
      (fun m : ℤ => if m = j then weight j else 0) := by
    funext m
    by_cases hm : m = j <;> simp [singleData, hm]
  rw [he]
  exact (hasSum_ite_eq j (weight j)).summable

theorem singleData_synthesis (j : ℤ) (x : ℝ) :
    (∑' m : ℤ, character x m • singleData j m) = character x j := by
  rw [tsum_eq_single j]
  · simp [singleData]
  · intro m hm
    simp [singleData, hm]

theorem negative_frequency_free_derivative :
    HasDerivAt (fun t : ℝ => phase t (-1)) (-Complex.I) 0 := by
  simpa [phase_zero] using phase_hasDerivAt 0 (-1)

def pairPotential (m : ℤ) : ℂ →L[ℂ] ℂ :=
  if m = 1 ∨ m = -1 then ContinuousLinearMap.id ℂ ℂ else 0

private theorem pairPotential_offsupport (m : ℤ)
    (hm : m ∉ ({1, -1} : Finset ℤ)) : pairPotential m = 0 := by
  have hn : m ≠ 1 ∧ m ≠ -1 := by simpa using hm
  simp [pairPotential, hn.1, hn.2]

theorem pairPotential_regular : RegularPotential pairPotential := by
  apply (hasSum_sum_of_ne_finset_zero (s := ({1, -1} : Finset ℤ))
    (f := fun m : ℤ => weight m * ‖pairPotential m‖) ?_).summable
  intro m hm
  simp only [pairPotential_offsupport m hm, norm_zero, mul_zero]

theorem pairPotential_hermitian : HermitianFourierPotential pairPotential := by
  intro m
  have hi : star (ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ := by
    change star (1 : ℂ →L[ℂ] ℂ) = 1
    simp
  have he : (-m = 1 ∨ -m = -1) ↔ (m = 1 ∨ m = -1) := by omega
  by_cases hm : m = 1 ∨ m = -1
  · simp only [pairPotential, if_pos hm, if_pos (he.mpr hm), hi]
  · simp only [pairPotential, if_neg hm, if_neg (not_congr he |>.mpr hm), star_zero]

theorem pairPotential_apply (x : ℝ) (z : ℂ) :
    operatorPotential pairPotential x z = character x 1 * z + character x (-1) * z := by
  rw [operatorPotential_apply pairPotential pairPotential_regular,
    tsum_eq_sum (s := ({1, -1} : Finset ℤ))]
  · norm_num [pairPotential, smul_eq_mul]
  · intro m hm
    simp only [pairPotential_offsupport m hm, _root_.zero_apply, smul_zero]

theorem pairPotential_at_zero : operatorPotential pairPotential 0 1 = 2 := by
  rw [pairPotential_apply]
  norm_num [character]

theorem pairPotential_at_pi : operatorPotential pairPotential Real.pi 1 = -2 := by
  rw [pairPotential_apply]
  have hp : character Real.pi 1 = -1 := by
    simpa [character, mul_comm] using Complex.exp_pi_mul_I
  have hn : character Real.pi (-1) = -1 := by
    simpa [character, mul_comm] using Complex.exp_neg_pi_mul_I
  rw [hp, hn]
  norm_num

theorem pairPotential_nonconstant :
    operatorPotential pairPotential 0 ≠ operatorPotential pairPotential Real.pi := by
  intro h
  have he := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  rw [pairPotential_at_zero, pairPotential_at_pi] at he
  norm_num at he

theorem pairPotential_selfAdjoint (x : ℝ) :
    IsSelfAdjoint (operatorPotential pairPotential x) :=
  operatorPotential_selfAdjoint pairPotential pairPotential_hermitian x

theorem zeroPotential_regular : RegularPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) := by
  simp [RegularPotential]

theorem zeroPotential_hermitian :
    HermitianFourierPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) := by
  intro m
  simp

theorem zeroPotential_field (x : ℝ) :
    operatorPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) x = 0 := by
  simp [operatorPotential]

def infiniteData (m : ℤ) : ℂ :=
  (1 / 2 : ℂ)^Encodable.encode m / (weight m : ℂ)

theorem infiniteData_norm (m : ℤ) :
    ‖infiniteData m‖ = (1 / 2 : ℝ)^Encodable.encode m / weight m := by
  simp [infiniteData, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (weight_pos m).le]

theorem infiniteData_weighted_norm (m : ℤ) :
    weight m * ‖infiniteData m‖ = (1 / 2 : ℝ)^Encodable.encode m := by
  rw [infiniteData_norm]
  exact mul_div_cancel₀ _ (weight_pos m).ne'

theorem infiniteData_regular :
    Summable (fun m : ℤ => weight m * ‖infiniteData m‖) := by
  simp only [infiniteData_weighted_norm]
  exact summable_geometric_two_encode

theorem infiniteData_nonzero (m : ℤ) : infiniteData m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [infiniteData_norm]
  have hw := weight_pos m
  positivity

theorem infiniteData_support_all : Function.support infiniteData = Set.univ := by
  ext m
  simp [Function.mem_support, infiniteData_nonzero]

theorem infiniteData_infinite_support : (Function.support infiniteData).Infinite := by
  rw [infiniteData_support_all]
  exact Set.infinite_univ

theorem variablePotential_singleMode_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi)
        (fun _ x => operatorPotential pairPotential x) 0 u ∧
      ∀ x, u 0 x = character x (-1) := by
  simpa only [singleData_synthesis] using
    global_classical_exists_unique pairPotential pairPotential_regular pairPotential_hermitian
      (singleData (-1)) (singleData_regular (-1))

theorem zeroPotential_infiniteData_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi) 0 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • infiniteData m := by
  have hz : (fun (_t x : ℝ) =>
      operatorPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) x) =
      (0 : ℝ → ℝ → ℂ →L[ℂ] ℂ) := by
    funext t x
    exact zeroPotential_field x
  have h := global_classical_exists_unique (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ))
    zeroPotential_regular zeroPotential_hermitian infiniteData infiniteData_regular
  rw [hz] at h
  exact h

theorem variablePotential_infiniteData_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi)
        (fun _ x => operatorPotential pairPotential x) 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • infiniteData m :=
  global_classical_exists_unique pairPotential pairPotential_regular pairPotential_hermitian
    infiniteData infiniteData_regular

end NDEAEvolve.Exp014.Controls


#print axioms NDEAEvolve.Exp014.strong_apply_hasDerivAt
#print axioms NDEAEvolve.Exp014.dysonTerm_continuous
#print axioms NDEAEvolve.Exp014.dysonTerm_succ_hasDerivAt
#print axioms NDEAEvolve.Exp014.dysonTerm_succ_zero
#print axioms NDEAEvolve.Exp014.dysonTerm_norm_le
#print axioms NDEAEvolve.Exp014.dysonTerm_summable
#print axioms NDEAEvolve.Exp014.linearEvolution_eq_head_add
#print axioms NDEAEvolve.Exp014.linearEvolution_zero
#print axioms NDEAEvolve.Exp014.linearEvolution_hasDerivAt
#print axioms NDEAEvolve.Exp014.operatorEvaluation_continuous
#print axioms NDEAEvolve.Exp014.exists_global_linear_solution
#print axioms NDEAEvolve.Exp014.weight_one_le
#print axioms NDEAEvolve.Exp014.weight_pos
#print axioms NDEAEvolve.Exp014.weight_ge_one
#print axioms NDEAEvolve.Exp014.abs_frequency_le_weight
#print axioms NDEAEvolve.Exp014.frequency_sq_le_weight
#print axioms NDEAEvolve.Exp014.abs_frequency_div_weight_le
#print axioms NDEAEvolve.Exp014.frequency_sq_div_weight_le
#print axioms NDEAEvolve.Exp014.weight_add_le
#print axioms NDEAEvolve.Exp014.weight_neg
#print axioms NDEAEvolve.Exp014.coefficientCLM_apply
#print axioms NDEAEvolve.Exp014.state_summable_norm
#print axioms NDEAEvolve.Exp014.state_tsum_norm
#print axioms NDEAEvolve.Exp014.coefficient_norm
#print axioms NDEAEvolve.Exp014.weight_mul_coefficient_norm
#print axioms NDEAEvolve.Exp014.weighted_summable
#print axioms NDEAEvolve.Exp014.weighted_tsum_norm
#print axioms NDEAEvolve.Exp014.ofCoefficients_apply
#print axioms NDEAEvolve.Exp014.coefficient_ofCoefficients
#print axioms NDEAEvolve.Exp014.ofCoefficients_norm
#print axioms NDEAEvolve.Exp014.coefficient_summable_norm
#print axioms NDEAEvolve.Exp014.coefficient_summable
#print axioms NDEAEvolve.Exp014.phase_norm
#print axioms NDEAEvolve.Exp014.phase_zero
#print axioms NDEAEvolve.Exp014.phase_add
#print axioms NDEAEvolve.Exp014.phase_continuous
#print axioms NDEAEvolve.Exp014.phase_hasDerivAt
#print axioms NDEAEvolve.Exp014.freeFlowLinear_apply
#print axioms NDEAEvolve.Exp014.freeFlowLinear_norm
#print axioms NDEAEvolve.Exp014.freeFlow_apply
#print axioms NDEAEvolve.Exp014.freeFlow_norm
#print axioms NDEAEvolve.Exp014.freeFlow_opNorm_le
#print axioms NDEAEvolve.Exp014.freeFlow_zero
#print axioms NDEAEvolve.Exp014.freeFlow_add
#print axioms NDEAEvolve.Exp014.freeFlow_neg_cancel
#print axioms NDEAEvolve.Exp014.freeFlow_isometry
#print axioms NDEAEvolve.Exp014.coefficient_freeFlow
#print axioms NDEAEvolve.Exp014.freeFlow_eq_tsum
#print axioms NDEAEvolve.Exp014.freeFlow_continuous
#print axioms NDEAEvolve.Exp014.freeFlow_joint_continuous
#print axioms NDEAEvolve.Exp014.scalarSeries_summable
#print axioms NDEAEvolve.Exp014.scalarSeriesCLM_apply
#print axioms NDEAEvolve.Exp014.scalarSeriesCLM_norm_le
#print axioms NDEAEvolve.Exp014.scalarSeries_norm_le
#print axioms NDEAEvolve.Exp014.scalarSeries_continuous
#print axioms NDEAEvolve.Exp014.scalarSeries_joint_continuous
#print axioms NDEAEvolve.Exp014.scalarSeries_hasDerivAt
#print axioms NDEAEvolve.Exp014.character_norm
#print axioms NDEAEvolve.Exp014.character_continuous
#print axioms NDEAEvolve.Exp014.character_hasDerivAt
#print axioms NDEAEvolve.Exp014.character_periodic
#print axioms NDEAEvolve.Exp014.character_add
#print axioms NDEAEvolve.Exp014.character_star
#print axioms NDEAEvolve.Exp014.potential_weight_add_le
#print axioms NDEAEvolve.Exp014.potential_weight_ratio_le
#print axioms NDEAEvolve.Exp014.potentialShift_apply
#print axioms NDEAEvolve.Exp014.potentialShift_norm_le
#print axioms NDEAEvolve.Exp014.coefficient_potentialShift
#print axioms NDEAEvolve.Exp014.potentialShift_summable_norm
#print axioms NDEAEvolve.Exp014.potentialShift_summable
#print axioms NDEAEvolve.Exp014.potentialConvolution_norm_le
#print axioms NDEAEvolve.Exp014.potentialConvolution_apply
#print axioms NDEAEvolve.Exp014.coefficient_potentialConvolution
#print axioms NDEAEvolve.Exp014.regularPotential_absolute
#print axioms NDEAEvolve.Exp014.operatorPotential_summable_norm
#print axioms NDEAEvolve.Exp014.operatorPotential_apply
#print axioms NDEAEvolve.Exp014.operatorPotential_norm_le
#print axioms NDEAEvolve.Exp014.operatorPotential_periodic
#print axioms NDEAEvolve.Exp014.operatorPotential_continuous
#print axioms NDEAEvolve.Exp014.operatorPotential_selfAdjoint
#print axioms NDEAEvolve.Exp014.synthesisMultiplier_norm
#print axioms NDEAEvolve.Exp014.synthesisMultiplier_bound
#print axioms NDEAEvolve.Exp014.firstMultiplier_bound
#print axioms NDEAEvolve.Exp014.secondMultiplier_bound
#print axioms NDEAEvolve.Exp014.synthesisMultiplier_continuous
#print axioms NDEAEvolve.Exp014.firstMultiplier_continuous
#print axioms NDEAEvolve.Exp014.secondMultiplier_continuous
#print axioms NDEAEvolve.Exp014.synthesisMultiplier_hasDerivAt
#print axioms NDEAEvolve.Exp014.firstMultiplier_hasDerivAt
#print axioms NDEAEvolve.Exp014.synth_eq_tsum
#print axioms NDEAEvolve.Exp014.synth_norm_le
#print axioms NDEAEvolve.Exp014.synth_joint_continuous
#print axioms NDEAEvolve.Exp014.synthFirst_joint_continuous
#print axioms NDEAEvolve.Exp014.synthSecond_joint_continuous
#print axioms NDEAEvolve.Exp014.synth_hasDerivAt
#print axioms NDEAEvolve.Exp014.synthFirst_hasDerivAt
#print axioms NDEAEvolve.Exp014.synth_periodic
#print axioms NDEAEvolve.Exp014.freeMultiplier_bound
#print axioms NDEAEvolve.Exp014.freeDerivativeMultiplier_bound
#print axioms NDEAEvolve.Exp014.freeMultiplier_hasDerivAt
#print axioms NDEAEvolve.Exp014.freeMultiplier_series
#print axioms NDEAEvolve.Exp014.freeDerivativeMultiplier_series
#print axioms NDEAEvolve.Exp014.synth_freeFlow_hasDerivAt
#print axioms NDEAEvolve.Exp014.synthesis_terms_summable
#print axioms NDEAEvolve.Exp014.synth_potentialShift
#print axioms NDEAEvolve.Exp014.synth_potentialConvolution
#print axioms NDEAEvolve.Exp014.interactionGenerator_apply
#print axioms NDEAEvolve.Exp014.interactionGenerator_bound
#print axioms NDEAEvolve.Exp014.interactionGenerator_joint_continuous
#print axioms NDEAEvolve.Exp014.interactionReal_norm_le
#print axioms NDEAEvolve.Exp014.interactingState_zero
#print axioms NDEAEvolve.Exp014.interactingState_hasDerivAt
#print axioms NDEAEvolve.Exp014.interactingState_continuous
#print axioms NDEAEvolve.Exp014.physicalState_continuous
#print axioms NDEAEvolve.Exp014.solution_zero
#print axioms NDEAEvolve.Exp014.solution_continuous
#print axioms NDEAEvolve.Exp014.solution_space_hasDerivAt
#print axioms NDEAEvolve.Exp014.solution_second_hasDerivAt
#print axioms NDEAEvolve.Exp014.solution_time_hasDerivAt
#print axioms NDEAEvolve.Exp014.solution_classical
#print axioms NDEAEvolve.Exp014.global_classical_exists_unique
#print axioms NDEAEvolve.Exp014.Controls.singleData_regular
#print axioms NDEAEvolve.Exp014.Controls.singleData_synthesis
#print axioms NDEAEvolve.Exp014.Controls.negative_frequency_free_derivative
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_regular
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_hermitian
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_apply
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_at_zero
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_at_pi
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_nonconstant
#print axioms NDEAEvolve.Exp014.Controls.pairPotential_selfAdjoint
#print axioms NDEAEvolve.Exp014.Controls.zeroPotential_regular
#print axioms NDEAEvolve.Exp014.Controls.zeroPotential_hermitian
#print axioms NDEAEvolve.Exp014.Controls.zeroPotential_field
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_norm
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_weighted_norm
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_regular
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_nonzero
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_support_all
#print axioms NDEAEvolve.Exp014.Controls.infiniteData_infinite_support
#print axioms NDEAEvolve.Exp014.Controls.variablePotential_singleMode_exists_unique
#print axioms NDEAEvolve.Exp014.Controls.zeroPotential_infiniteData_exists_unique
#print axioms NDEAEvolve.Exp014.Controls.variablePotential_infiniteData_exists_unique
