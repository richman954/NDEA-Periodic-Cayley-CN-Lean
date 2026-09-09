import Continuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp010
open scoped ComplexInnerProductSpace
namespace NDEAEvolve.Exp011.Probe

theorem potential_selfadjoint :
    IsSelfAdjoint (operatorOf (Exp007.Z + Exp007.X)) := by
  change star (operatorOf (Exp007.Z + Exp007.X)) = _
  simpa only [operatorOf, map_star] using
    congrArg (fun M : Mat 2 => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M)
      (hermitian_star (Exp007.Z_isHermitian.add Exp007.X_isHermitian))

theorem potential_cancellation (w : E 2) :
    (inner ℂ w ((-Complex.I) • operatorOf (Exp007.Z + Exp007.X) w)).re = 0 := by
  have h := potential_selfadjoint.isSymmetric.im_inner_self_apply w
  simpa [inner_smul_right, Complex.mul_re] using h

theorem imaginary_self_cancellation (w : E 2) :
    (inner ℂ w (Complex.I • w)).re = 0 := by
  simp [inner_smul_right, Complex.mul_re, inner_self_eq_norm_sq_to_K]

theorem periodic_deriv {f : ℝ → E 2} {L : ℝ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  have hd := (hf (x + L)).hasDerivAt.comp x ((hasDerivAt_id x).add_const L)
  have he : (fun y => f (y + L)) = f := funext hp
  simpa only [Function.comp_def, one_mul, mul_one, he] using hd.deriv.symm

def flux (u : ℝ → ℝ → E 2) (t x : ℝ) : ℝ :=
  2 * (inner ℂ (u t x) (Complex.I • deriv (u t) x)).re

theorem flux_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (t x : ℝ) :
    HasDerivAt (flux u t)
      (2 * (inner ℂ (u t x) (Complex.I • deriv (deriv (u t)) x)).re) x := by
  have hd := (hu.space_differentiable t x).hasDerivAt.inner ℂ
    ((hu.second_space_differentiable t x).hasDerivAt.const_smul Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have h := hr.const_mul 2
  simpa [flux, Complex.add_re, imaginary_self_cancellation] using h

end NDEAEvolve.Exp011.Probe
