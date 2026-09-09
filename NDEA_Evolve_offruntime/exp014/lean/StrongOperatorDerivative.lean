import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Module

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
