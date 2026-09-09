import CombinedVerification
import ReducedNoncommuting
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp007

local instance (n : ℕ) : NormedAlgebra ℚ (E n →L[ℂ] E n) :=
  NormedAlgebra.restrictScalars ℚ ℂ (E n →L[ℂ] E n)

def continuumPropagator {n : ℕ} (H : Mat n) (t : ℝ) : E n →L[ℂ] E n :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • operatorOf H)

theorem continuumPropagator_eq_exactStepHat {n : ℕ} (H : Mat n) (t : ℝ) :
    continuumPropagator H t = exactStepHat H (t / 2) := by
  unfold continuumPropagator exactStepHat skewHat
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => NormedSpace.exp (z • operatorOf H))
  push_cast
  ring

theorem continuumPropagator_add {n : ℕ} (H : Mat n) (s t : ℝ) :
    continuumPropagator H (s + t) = continuumPropagator H s * continuumPropagator H t := by
  unfold continuumPropagator
  have hc : Commute ((-Complex.I * (s : ℂ)) • operatorOf H)
      ((-Complex.I * (t : ℂ)) • operatorOf H) :=
    by
      apply ContinuousLinearMap.ext
      intro w
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]
      rw [smul_smul, smul_smul, mul_comm]
  rw [← NormedSpace.exp_add_of_commute hc]
  congr 1
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  push_cast
  module

theorem continuumEvolution_hasDerivAt {n : ℕ} (H : Mat n) (v0 : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => continuumPropagator H s v0)
      ((-Complex.I) • operatorOf H (continuumPropagator H t v0)) t := by
  let K : E n →L[ℂ] E n := (-Complex.I) • operatorOf H
  have hc := (hasDerivAt_exp_smul_const' K (t : ℂ)).clm_apply
    (hasDerivAt_const (t : ℂ) v0)
  have hr := hc.scomp t Complex.ofRealCLM.hasDerivAt
  simpa [K, continuumPropagator, smul_smul, mul_comm, Function.comp_def,
    ContinuousLinearMap.mul_apply] using! hr


/-- Arbitrary initial spinor evolved by the continuum Fourier-mode Hamiltonian. -/
def v (v0 : E 2) (t : ℝ) : E 2 := continuumPropagator (A0 + B) t v0

/-- A periodic spinor-valued continuum solution. -/
def U (v0 : E 2) (t x : ℝ) : E 2 := Exp006.phase x • v v0 t

@[simp] theorem v_initial (v0 : E 2) : v v0 0 = v0 := by
  have hz : (-Complex.I * (0 : ℂ)) • operatorOf (A0 + B) =
      (0 : E 2 →L[ℂ] E 2) := by
    apply ContinuousLinearMap.ext
    intro w
    change (-Complex.I * (0 : ℂ)) • (operatorOf (A0 + B) w) = 0
    simp
  change NormedSpace.exp ((-Complex.I * (0 : ℂ)) • operatorOf (A0 + B)) v0 = v0
  rw [hz, NormedSpace.exp_zero]
  rfl

@[simp] theorem U_initial (v0 : E 2) (x : ℝ) :
    U v0 0 x = Exp006.phase x • v0 := by simp [U]

theorem U_periodic (v0 : E 2) (t : ℝ) : Function.Periodic (U v0 t) (2 * Real.pi) := by
  intro x
  simp only [U, Exp006.phase_periodic x]

theorem v_hasDerivAt (v0 : E 2) (t : ℝ) :
    HasDerivAt (v v0) ((-Complex.I) • operatorOf (A0 + B) (v v0 t)) t :=
  continuumEvolution_hasDerivAt (A0 + B) v0 t

theorem U_time_hasDerivAt (v0 : E 2) (t x : ℝ) :
    HasDerivAt (fun s => U v0 s x)
      (Exp006.phase x • ((-Complex.I) • operatorOf (A0 + B) (v v0 t))) t := by
  exact (v_hasDerivAt v0 t).const_smul (Exp006.phase x)

theorem U_space_hasDerivAt (v0 : E 2) (t x : ℝ) :
    HasDerivAt (U v0 t) ((Exp006.phase x * Complex.I) • v v0 t) x := by
  exact (Exp006.phase_hasDerivAt x).smul_const (v v0 t)

theorem U_second_derivative (v0 : E 2) (t x : ℝ) :
    deriv (deriv (U v0 t)) x = - U v0 t x := by
  have hd : deriv (U v0 t) = fun y => (Exp006.phase y * Complex.I) • v v0 t :=
    funext fun y => (U_space_hasDerivAt v0 t y).deriv
  rw [hd, (((Exp006.phase_hasDerivAt x).mul_const Complex.I).smul_const (v v0 t)).deriv]
  simp [U, mul_assoc]

theorem v_norm (v0 : E 2) (t : ℝ) : ‖v v0 t‖ = ‖v0‖ := by
  unfold v
  rw [continuumPropagator_eq_exactStepHat]
  exact ContinuousLinearMap.norm_map_of_mem_unitary
    (exactStepHat_mem_unitary (t / 2) (A0 + B)
      ((A_isHermitian 1).add B_isHermitian)) v0

theorem U_norm (v0 : E 2) (t x : ℝ) : ‖U v0 t x‖ = ‖v0‖ := by
  simp [U, norm_smul, v_norm]

/-- The actual real derivatives solve the spinor Schrödinger PDE. -/
theorem U_schrodinger (v0 : E 2) (t x : ℝ) :
    Complex.I • deriv (fun s => U v0 s x) t =
      -deriv (deriv (U v0 t)) x + operatorOf (Z + X) (U v0 t x) := by
  rw [(U_time_hasDerivAt v0 t x).deriv, U_second_derivative, neg_neg]
  have hi : Complex.I * (Exp006.phase x * (-Complex.I)) = Exp006.phase x := by
    calc
      _ = -(Complex.I * Complex.I) * Exp006.phase x := by ring
      _ = _ := by simp
  rw [smul_smul, smul_smul, mul_assoc, hi]
  have hH : A0 + B = 1 + (Z + X) := by simp [A0, A, B, add_assoc]
  rw [hH]
  simp [operatorOf, U, smul_add]

theorem v_exact_step (v0 : E 2) (t k : ℝ) :
    exactStepHat (A0 + B) (k / 2) (v v0 t) = v v0 (t + k) := by
  rw [← continuumPropagator_eq_exactStepHat]
  unfold v
  rw [add_comm t k, continuumPropagator_add, ContinuousLinearMap.mul_apply]

#print axioms continuumEvolution_hasDerivAt
#print axioms U_schrodinger
#print axioms U_second_derivative
#print axioms U_periodic
#print axioms U_initial
#print axioms U_norm
#print axioms v_exact_step
end NDEAEvolve.Exp007
