import StageBridge

/-! Exact defects for the existing ordered A-half/B-full/A-half Cayley step.
No commuting reduction and no residual-smallness premise is used. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def stageResidual (A : E →L[ℂ] E) (a : ℝ) (u v : E) : E :=
  v - u + (Complex.I * (a : ℂ)) • A (v + u)

def endpointMean (u₀ u₃ : E) : E := (1 / 2 : ℂ) • (u₀ + u₃)

def internalMeanDefect (u₀ u₁ u₂ u₃ : E) : E :=
  (1 / 2 : ℂ) • (u₁ + u₂ - u₀ - u₃)

/-- The exact scaled midpoint defect includes both solve and splitting terms. -/
theorem ordered_stage_midpoint_defect (A B : E →L[ℂ] E) (k : ℝ)
    (u₀ u₁ u₂ u₃ : E) :
    Complex.I • (u₃ - u₀) - (k : ℂ) • (A + B) (endpointMean u₀ u₃) =
      Complex.I • (stageResidual A (k / 4) u₀ u₁ +
        stageResidual B (k / 2) u₁ u₂ + stageResidual A (k / 4) u₂ u₃) +
      (k : ℂ) • ((1 / 2 : ℂ) • A (internalMeanDefect u₀ u₁ u₂ u₃) +
        B (internalMeanDefect u₀ u₁ u₂ u₃)) := by
  simp only [stageResidual, endpointMean, internalMeanDefect,
    ContinuousLinearMap.add_apply, map_add, map_sub, map_smul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

section ActualCayley
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- This is the old full-grid denominator residual, with its normalization intact. -/
theorem stageResidual_eq_gridFactorResidual (A : Matrix ι ι ℂ)
    (a : ℝ) (u v : Vec ι) :
    stageResidual (op A) a u v = NDEAEvolve.Exp007.gridFactorResidual A a u v := by
  simp only [stageResidual, NDEAEvolve.Exp007.gridFactorResidual, den, num,
    map_add, map_sub, map_one, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, smul_add]
  module

theorem stageResidual_actual_cayley_zero (A : Matrix ι ι ℂ) (a : ℝ)
    (hA : A.IsHermitian) (u : Vec ι) :
    stageResidual (op A) a u (step a A u) = 0 := by
  rw [stageResidual_eq_gridFactorResidual]
  exact NDEAEvolve.Exp008.gridFactorResidual_step_zero A a hA u

/-- Immediate consumer: the actual ordered Hermitian Cayley stages. -/
theorem actual_symmetric_midpoint_defect (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    let u₁ := step (k / 4) A u₀
    let u₂ := step (k / 2) B u₁
    let u₃ := step (k / 4) A u₂
    Complex.I • (u₃ - u₀) - (k : ℂ) • (op A + op B) (endpointMean u₀ u₃) =
      (k : ℂ) • ((1 / 2 : ℂ) • op A (internalMeanDefect u₀ u₁ u₂ u₃) +
        op B (internalMeanDefect u₀ u₁ u₂ u₃)) := by
  dsimp only
  have h := ordered_stage_midpoint_defect (op A) (op B) k u₀
    (step (k / 4) A u₀) (step (k / 2) B (step (k / 4) A u₀))
    (step (k / 4) A (step (k / 2) B (step (k / 4) A u₀)))
  simpa only [stageResidual_actual_cayley_zero A (k / 4) hA,
    stageResidual_actual_cayley_zero B (k / 2) hB, add_zero, smul_zero, zero_add] using h

end ActualCayley
end NDEAEvolve.Exp016
