import NDEAMathlibGate.PeriodicLaplacian1DV1R2_ExplicitSBP
import Mathlib.Analysis.Calculus.Taylor

/-! Production V1: interval-to-global degree-three Taylor bridge. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEAIntervalToGlobalTaylorBridgeProbe

def cubicGlobal
    (a0 a1 a2 a3 : ℂ)
    (h : ℝ) :
    ℂ :=
  a0
    + (h : ℂ) * a1
    + ((h : ℂ) ^ 2 / 2) * a2
    + ((h : ℂ) ^ 3 / 6) * a3

def cubicWithin
    (u : ℝ → ℂ)
    (s : Set ℝ)
    (x : ℝ)
    (h : ℝ) :
    ℂ :=
  u x
    + (h : ℂ) * iteratedDerivWithin 1 u s x
    + ((h : ℂ) ^ 2 / 2) * iteratedDerivWithin 2 u s x
    + ((h : ℂ) ^ 3 / 6) * iteratedDerivWithin 3 u s x

def cubicOfFunction
    (u : ℝ → ℂ)
    (x h : ℝ) :
    ℂ :=
  cubicGlobal
    (u x)
    (iteratedDeriv 1 u x)
    (iteratedDeriv 2 u x)
    (iteratedDeriv 3 u x)
    h

def taylorPlus
    (u : ℝ → ℂ)
    (x h : ℝ) :
    ℂ :=
  taylorWithinEval u 3 (Set.uIcc x (x + h)) x (x + h)

def taylorMinus
    (u : ℝ → ℂ)
    (x h : ℝ) :
    ℂ :=
  taylorWithinEval u 3 (Set.uIcc x (x - h)) x (x - h)

theorem taylor_degree3_within
    (u : ℝ → ℂ)
    (s : Set ℝ)
    (x h : ℝ) :
    taylorWithinEval u 3 s x (x + h) = cubicWithin u s x h := by
  simp [
    taylor_within_apply,
    cubicWithin,
    Finset.sum_range_succ,
    Complex.real_smul
  ] <;> ring

private theorem uniqueDiffOn_plus
    (x h : ℝ)
    (hh : 0 < h) :
    UniqueDiffOn ℝ (Set.uIcc x (x + h)) := by
  rw [Set.uIcc_of_le (by linarith)]
  exact uniqueDiffOn_Icc (by linarith)

private theorem uniqueDiffOn_minus
    (x h : ℝ)
    (hh : 0 < h) :
    UniqueDiffOn ℝ (Set.uIcc x (x - h)) := by
  rw [Set.uIcc_of_ge (by linarith : x - h ≤ x)]
  exact uniqueDiffOn_Icc (by linarith)

theorem taylorPlus_eq_cubicOfFunction
    (u : ℝ → ℂ)
    (x h : ℝ)
    (hu : ContDiff ℝ 4 u)
    (hh : 0 < h) :
    taylorPlus u x h = cubicOfFunction u x h := by
  have h1 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 1)
    (uniqueDiffOn_plus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  have h2 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 2)
    (uniqueDiffOn_plus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  have h3 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 3)
    (uniqueDiffOn_plus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  calc
    taylorPlus u x h = cubicWithin u (Set.uIcc x (x + h)) x h := by
      exact taylor_degree3_within u (Set.uIcc x (x + h)) x h
    _ = cubicOfFunction u x h := by
      unfold cubicWithin cubicOfFunction cubicGlobal
      rw [h1, h2, h3]

theorem taylorMinus_eq_cubicOfFunction
    (u : ℝ → ℂ)
    (x h : ℝ)
    (hu : ContDiff ℝ 4 u)
    (hh : 0 < h) :
    taylorMinus u x h = cubicOfFunction u x (-h) := by
  have h1 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 1)
    (uniqueDiffOn_minus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  have h2 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 2)
    (uniqueDiffOn_minus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  have h3 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 3)
    (uniqueDiffOn_minus x h hh)
    (hu.contDiffAt.of_le (by norm_num))
    Set.left_mem_uIcc
  calc
    taylorMinus u x h = cubicWithin u (Set.uIcc x (x - h)) x (-h) := by
      simpa [taylorMinus, sub_eq_add_neg] using
        taylor_degree3_within u (Set.uIcc x (x - h)) x (-h)
    _ = cubicOfFunction u x (-h) := by
      unfold cubicWithin cubicOfFunction cubicGlobal
      rw [h1, h2, h3]

#check taylorPlus_eq_cubicOfFunction
#check taylorMinus_eq_cubicOfFunction
#print axioms taylorPlus_eq_cubicOfFunction
#print axioms taylorMinus_eq_cubicOfFunction

end NDEAIntervalToGlobalTaylorBridgeProbe
