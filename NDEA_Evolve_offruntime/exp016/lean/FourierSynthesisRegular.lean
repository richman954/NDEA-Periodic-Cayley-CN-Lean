import RegularSynthesis
import FourierReconstruction
import ContinuumModes

/-! The actual full-grid Fourier interpolation supplies the spatial regularity
contract. Its derivative maps are computed finite sums, with no consistency
or refinement assumption. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

def nodeValueLinear (n : ℕ) (j : Fin (n+1)) : Vec (Grid n) →ₗ[ℂ] E 2 where
  toFun := fun y => Exp011.nodeValue n y j
  map_add' := by intro u v; ext b; rfl
  map_smul' := by intro c v; ext b; rfl

def nodeValueCLM (n : ℕ) (j : Fin (n+1)) : Vec (Grid n) →L[ℂ] E 2 :=
  (nodeValueLinear n j).toContinuousLinearMap

@[simp] theorem nodeValueCLM_apply (n : ℕ) (j : Fin (n+1)) (y : Vec (Grid n)) :
    nodeValueCLM n j y = Exp011.nodeValue n y j := rfl

def fourierCoefficientCLM (M : ℕ) (h : ℝ) (m : Fin (2*M+1)) :
    Vec (Grid (2*M)) →L[ℂ] E 2 :=
  ((2*M+1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin (2*M+1),
    phase (-((oddFrequency M m : ℝ)*((j.val : ℝ)*h))) • nodeValueCLM (2*M) j

@[simp] theorem fourierCoefficientCLM_apply (M : ℕ) (h : ℝ)
    (m : Fin (2*M+1)) (y : Vec (Grid (2*M))) :
    fourierCoefficientCLM M h m y = fourierCoefficient M h y m := by
  simp [fourierCoefficientCLM, fourierCoefficient]

def fourierEval (M : ℕ) (h x : ℝ) : Vec (Grid (2*M)) →L[ℂ] E 2 :=
  ∑ m : Fin (2*M+1), phase ((oddFrequency M m : ℝ)*x) • fourierCoefficientCLM M h m

def fourierDx (M : ℕ) (h x : ℝ) : Vec (Grid (2*M)) →L[ℂ] E 2 :=
  ∑ m : Fin (2*M+1),
    (phase ((oddFrequency M m : ℝ)*x)*Complex.I*(oddFrequency M m : ℂ)) •
      fourierCoefficientCLM M h m

def fourierDxx (M : ℕ) (h x : ℝ) : Vec (Grid (2*M)) →L[ℂ] E 2 :=
  ∑ m : Fin (2*M+1),
    (phase ((oddFrequency M m : ℝ)*x)*Complex.I*(oddFrequency M m : ℂ)*
      Complex.I*(oddFrequency M m : ℂ)) • fourierCoefficientCLM M h m

@[simp] theorem fourierEval_apply (M : ℕ) (h x : ℝ) (y : Vec (Grid (2*M))) :
    fourierEval M h x y = fourierReconstruction M h y x := by
  simp [fourierEval, fourierReconstruction, fourierSynthesis]

theorem fourierEval_continuous (M : ℕ) (h : ℝ) : Continuous (fourierEval M h) := by
  apply continuous_finset_sum
  intro m _
  exact (continuous_iff_continuousAt.mpr fun x =>
    (phaseMode_hasDerivAt (oddFrequency M m) x).continuousAt).smul continuous_const

theorem fourierDx_continuous (M : ℕ) (h : ℝ) : Continuous (fourierDx M h) := by
  apply continuous_finset_sum
  intro m _
  exact (((continuous_iff_continuousAt.mpr fun x =>
    (phaseMode_hasDerivAt (oddFrequency M m) x).continuousAt).mul continuous_const).mul
      continuous_const).smul continuous_const

theorem fourierDxx_continuous (M : ℕ) (h : ℝ) : Continuous (fourierDxx M h) := by
  apply continuous_finset_sum
  intro m _
  exact (((((continuous_iff_continuousAt.mpr fun x =>
    (phaseMode_hasDerivAt (oddFrequency M m) x).continuousAt).mul continuous_const).mul
      continuous_const).mul continuous_const).mul continuous_const).smul continuous_const

theorem fourierEval_hasDerivAt (M : ℕ) (h x : ℝ) (y : Vec (Grid (2*M))) :
    HasDerivAt (fun z => fourierEval M h z y) (fourierDx M h x y) x := by
  simpa only [fourierEval, fourierDx, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply] using
    HasDerivAt.fun_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin (2*M+1)))) =>
      (phaseMode_hasDerivAt (oddFrequency M m) x).smul_const
        (fourierCoefficientCLM M h m y))

theorem fourierDx_hasDerivAt (M : ℕ) (h x : ℝ) (y : Vec (Grid (2*M))) :
    HasDerivAt (fun z => fourierDx M h z y) (fourierDxx M h x y) x := by
  simpa only [fourierDx, fourierDxx, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply] using
    HasDerivAt.fun_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin (2*M+1)))) =>
      (((phaseMode_hasDerivAt (oddFrequency M m) x).mul_const Complex.I).mul_const
        (oddFrequency M m : ℂ)).smul_const (fourierCoefficientCLM M h m y))

theorem fourierEval_periodic (M : ℕ) (h : ℝ) :
    Function.Periodic (fourierEval M h) (2*Real.pi) := by
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simpa only [fourierEval_apply] using fourierReconstruction_periodic M h y x

/-- Concrete Fourier consumer of the regularity contract, on every full odd grid. -/
def fourierRegularSynthesis (M : ℕ) (h : ℝ) :
    RegularSynthesis (Vec (Grid (2*M))) (E 2) (2*Real.pi) where
  eval := fourierEval M h
  dx := fourierDx M h
  dxx := fourierDxx M h
  continuous_eval := fourierEval_continuous M h
  continuous_dx := fourierDx_continuous M h
  continuous_dxx := fourierDxx_continuous M h
  derivative_eval := fourierEval_hasDerivAt M h
  derivative_dx := fourierDx_hasDerivAt M h
  periodic_eval := fourierEval_periodic M h

@[simp] theorem fourierRegularSynthesis_eval (M : ℕ) (h x : ℝ)
    (y : Vec (Grid (2*M))) :
    (fourierRegularSynthesis M h).eval x y = fourierReconstruction M h y x :=
  fourierEval_apply M h x y

theorem fourierRegularSynthesis_field (M : ℕ) (h : ℝ)
    (q : ℝ → Vec (Grid (2*M))) :
    (fourierRegularSynthesis M h).field q = fun t => fourierReconstruction M h (q t) := by
  funext t x
  exact fourierRegularSynthesis_eval M h x (q t)

theorem fourier_quadratic_regular (M : ℕ) (h : ℝ)
    (G : Vec (Grid (2*M)) →L[ℂ] Vec (Grid (2*M)))
    (m v : Vec (Grid (2*M))) (t₀ k : ℝ) :
    Exp015.IsRegularPeriodicField (2*Real.pi)
      (fun t => fourierReconstruction M h (quadraticTime G m v t₀ k t)) := by
  rw [← fourierRegularSynthesis_field]
  exact (fourierRegularSynthesis M h).quadratic_field_regular G m v t₀ k

#print axioms fourierEval_apply
#print axioms fourierEval_hasDerivAt
#print axioms fourierDx_hasDerivAt
#print axioms fourierEval_periodic
#print axioms fourierRegularSynthesis_eval
#print axioms fourierRegularSynthesis_field
#print axioms fourier_quadratic_regular
end NDEAEvolve.Exp016
