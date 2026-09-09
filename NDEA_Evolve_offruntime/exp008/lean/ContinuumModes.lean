import Exp007Foundation

/-! Finite Fourier superpositions of the spinor Schrödinger equation.
Every frequency is an arbitrary signed integer; no separation or non-aliasing
assumption is needed for this continuum construction. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp008

local instance (n : ℕ) : NormedAlgebra ℚ (E n →L[ℂ] E n) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E n →L[ℂ] E n)

def modeGenerator (m : ℤ) : Mat 2 := Exp007.A ((m : ℝ)^2) + Exp007.B

theorem modeGenerator_isHermitian (m : ℤ) : (modeGenerator m).IsHermitian :=
  (Exp007.A_isHermitian _).add Exp007.B_isHermitian

def modeOrbit (m : ℤ) (t : ℝ) (v : E 2) : E 2 :=
  exactStepHat (modeGenerator m) (t / 2) v

theorem modeOrbit_eq_continuum (m : ℤ) (t : ℝ) (v : E 2) :
    modeOrbit m t v = Exp007.continuumPropagator (modeGenerator m) t v := by
  rw [Exp007.continuumPropagator_eq_exactStepHat]
  rfl

@[simp] theorem modeOrbit_initial (m : ℤ) (v : E 2) : modeOrbit m 0 v = v := by
  rw [modeOrbit_eq_continuum]
  have hz : (0 : ℂ) • operatorOf (modeGenerator m) = (0 : E 2 →L[ℂ] E 2) := by
    apply ContinuousLinearMap.ext
    intro w
    change (0 : ℂ) • operatorOf (modeGenerator m) w = 0
    simp
  simp only [Exp007.continuumPropagator, Complex.ofReal_zero, mul_zero]
  rw [hz, NormedSpace.exp_zero]
  rfl

theorem modeOrbit_hasDerivAt (m : ℤ) (v : E 2) (t : ℝ) :
    HasDerivAt (fun s => modeOrbit m s v)
      ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t v)) t := by
  simpa only [modeOrbit_eq_continuum] using
    Exp007.continuumEvolution_hasDerivAt (modeGenerator m) v t

@[simp] theorem modeOrbit_norm (m : ℤ) (t : ℝ) (v : E 2) :
    ‖modeOrbit m t v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (exactStepHat_mem_unitary (t / 2) (modeGenerator m) (modeGenerator_isHermitian m)) v

theorem modeOrbit_exact_step (m : ℤ) (v : E 2) (t k : ℝ) :
    exactStepHat (modeGenerator m) (k / 2) (modeOrbit m t v) =
      modeOrbit m (t + k) v := by
  rw [modeOrbit_eq_continuum, modeOrbit_eq_continuum,
    ← Exp007.continuumPropagator_eq_exactStepHat, add_comm t k,
    Exp007.continuumPropagator_add, ContinuousLinearMap.mul_apply]

def modeSolution (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  Exp006.phase ((m : ℝ) * x) • modeOrbit m t v

theorem phaseMode_periodic (m : ℤ) :
    Function.Periodic (fun x : ℝ => Exp006.phase ((m : ℝ) * x)) (2 * Real.pi) := by
  intro x
  simpa only [mul_add] using (Exp006.phase_periodic.int_mul m) ((m : ℝ) * x)

theorem phaseMode_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Exp006.phase ((m : ℝ) * y))
      (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) x := by
  simpa [Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using!
    (Exp006.phase_hasDerivAt ((m : ℝ) * x)).scomp x
      ((hasDerivAt_id x).const_mul (m : ℝ))

@[simp] theorem modeSolution_initial (m : ℤ) (v : E 2) (x : ℝ) :
    modeSolution m v 0 x = Exp006.phase ((m : ℝ) * x) • v := by
  simp [modeSolution]

theorem modeSolution_periodic (m : ℤ) (v : E 2) (t : ℝ) :
    Function.Periodic (modeSolution m v t) (2 * Real.pi) := by
  intro x
  simp only [modeSolution, phaseMode_periodic m x]

@[simp] theorem modeSolution_norm (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSolution m v t x‖ = ‖v‖ := by
  simp [modeSolution, norm_smul]

theorem modeSolution_time_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (fun s => modeSolution m v s x)
      (Exp006.phase ((m : ℝ) * x) •
        ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t v))) t := by
  exact (modeOrbit_hasDerivAt m v t).const_smul (Exp006.phase ((m : ℝ) * x))

theorem modeSolution_space_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSolution m v t)
      ((Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) • modeOrbit m t v) x :=
  (phaseMode_hasDerivAt m x).smul_const _

theorem modeSolution_second_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (deriv (modeSolution m v t))
      (-((m : ℂ)^2) • modeSolution m v t x) x := by
  have hd : deriv (modeSolution m v t) = fun y =>
      (Exp006.phase ((m : ℝ) * y) * Complex.I * (m : ℂ)) • modeOrbit m t v :=
    funext fun y => (modeSolution_space_hasDerivAt m v t y).deriv
  rw [hd]
  have hc : (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) *
      Complex.I * (m : ℂ) = -((m : ℂ)^2) * Exp006.phase ((m : ℝ) * x) := by
    calc
      _ = (Complex.I * Complex.I) * ((m : ℂ)^2 * Exp006.phase ((m : ℝ) * x)) := by ring
      _ = _ := by simp
  simpa only [modeSolution, smul_smul, hc] using
    (((phaseMode_hasDerivAt m x).mul_const Complex.I).mul_const (m : ℂ)).smul_const
      (modeOrbit m t v)

theorem modeSolution_second_derivative (m : ℤ) (v : E 2) (t x : ℝ) :
    deriv (deriv (modeSolution m v t)) x = -((m : ℂ)^2) • modeSolution m v t x :=
  (modeSolution_second_hasDerivAt m v t x).deriv

theorem modeGenerator_apply (m : ℤ) (w : E 2) :
    operatorOf (modeGenerator m) w =
      (m : ℂ)^2 • w + operatorOf (Exp007.Z + Exp007.X) w := by
  simp [modeGenerator, Exp007.A, Exp007.B, operatorOf, add_assoc]

/-- The PDE uses the actual first real time derivative and second real space derivative. -/
theorem modeSolution_schrodinger (m : ℤ) (v : E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => modeSolution m v s x) t =
      -deriv (deriv (modeSolution m v t)) x +
        operatorOf (Exp007.Z + Exp007.X) (modeSolution m v t x) := by
  rw [(modeSolution_time_hasDerivAt m v t x).deriv, modeSolution_second_derivative]
  have hi : Complex.I * (Exp006.phase ((m : ℝ) * x) * (-Complex.I)) =
      Exp006.phase ((m : ℝ) * x) := by
    calc
      _ = -(Complex.I * Complex.I) * Exp006.phase ((m : ℝ) * x) := by ring
      _ = _ := by simp
  rw [smul_smul, smul_smul, mul_assoc, hi, modeGenerator_apply]
  simp [modeSolution, smul_add, smul_smul, mul_comm]

def finiteSolution (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  ∑ m ∈ S, modeSolution m (a m) t x

@[simp] theorem finiteSolution_initial (S : Finset ℤ) (a : ℤ → E 2) (x : ℝ) :
    finiteSolution S a 0 x = ∑ m ∈ S, Exp006.phase ((m : ℝ) * x) • a m := by
  simp [finiteSolution]

theorem finiteSolution_periodic (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    Function.Periodic (finiteSolution S a t) (2 * Real.pi) := by
  intro x
  exact Finset.sum_congr rfl fun m _ => modeSolution_periodic m (a m) t x

theorem finiteSolution_time_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (fun s => finiteSolution S a s x)
      (∑ m ∈ S, Exp006.phase ((m : ℝ) * x) •
        ((-Complex.I) • operatorOf (modeGenerator m) (modeOrbit m t (a m)))) t :=
  HasDerivAt.fun_sum fun m _ => modeSolution_time_hasDerivAt m (a m) t x

theorem finiteSolution_space_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (finiteSolution S a t)
      (∑ m ∈ S, (Exp006.phase ((m : ℝ) * x) * Complex.I * (m : ℂ)) •
        modeOrbit m t (a m)) x :=
  HasDerivAt.fun_sum fun m _ => modeSolution_space_hasDerivAt m (a m) t x

theorem finiteSolution_derivative_sum (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    deriv (finiteSolution S a t) = fun x => ∑ m ∈ S, deriv (modeSolution m (a m) t) x := by
  funext x
  rw [(finiteSolution_space_hasDerivAt S a t x).deriv]
  exact Finset.sum_congr rfl fun m _ => (modeSolution_space_hasDerivAt m (a m) t x).deriv.symm

theorem finiteSolution_second_hasDerivAt (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    HasDerivAt (deriv (finiteSolution S a t))
      (∑ m ∈ S, -((m : ℂ)^2) • modeSolution m (a m) t x) x := by
  rw [finiteSolution_derivative_sum]
  exact HasDerivAt.fun_sum fun m _ => modeSolution_second_hasDerivAt m (a m) t x

theorem finiteSolution_second_derivative (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    deriv (deriv (finiteSolution S a t)) x =
      ∑ m ∈ S, -((m : ℂ)^2) • modeSolution m (a m) t x :=
  (finiteSolution_second_hasDerivAt S a t x).deriv

/-- Every finite signed Fourier superposition solves the same continuum PDE. -/
theorem finiteSolution_schrodinger (S : Finset ℤ) (a : ℤ → E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => finiteSolution S a s x) t =
      -deriv (deriv (finiteSolution S a t)) x +
        operatorOf (Exp007.Z + Exp007.X) (finiteSolution S a t x) := by
  rw [(finiteSolution_time_hasDerivAt S a t x).deriv, finiteSolution_second_derivative]
  simp only [finiteSolution, Finset.smul_sum, map_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simpa only [(modeSolution_time_hasDerivAt m (a m) t x).deriv,
    modeSolution_second_derivative] using modeSolution_schrodinger m (a m) t x

#print axioms modeGenerator_isHermitian
#print axioms modeOrbit_initial
#print axioms modeOrbit_hasDerivAt
#print axioms modeOrbit_norm
#print axioms modeOrbit_exact_step
#print axioms phaseMode_periodic
#print axioms modeSolution_second_derivative
#print axioms modeSolution_schrodinger
#print axioms finiteSolution_initial
#print axioms finiteSolution_periodic
#print axioms finiteSolution_time_hasDerivAt
#print axioms finiteSolution_second_derivative
#print axioms finiteSolution_schrodinger
end NDEAEvolve.Exp008
