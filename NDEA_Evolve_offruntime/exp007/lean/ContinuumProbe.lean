import CombinedVerification
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

#print axioms continuumEvolution_hasDerivAt
end NDEAEvolve.Exp007
