import SplitDefect
import QuadraticTime

/-! The quadratic endpoint defect for the actual ordered Cayley stages.
Solve residuals and the internal-stage defect have their exact normalization.
The scalar control has exact solves and a nonzero unsplit CN defect. -/
noncomputable section
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def quadraticMidpointDefect (H : E →L[ℂ] E) (u₀ u₃ : E) (k : ℝ) : E :=
  Complex.I • quadraticVelocity u₀ u₃ k - H (quadraticMean u₀ u₃)

theorem quadraticMidpointDefect_eq_stageResiduals (A B : E →L[ℂ] E)
    (k : ℝ) (hk : k ≠ 0) (u₀ u₁ u₂ u₃ : E) :
    quadraticMidpointDefect (A + B) u₀ u₃ k =
      (Complex.I / (k : ℂ)) • (stageResidual A (k / 4) u₀ u₁ +
        stageResidual B (k / 2) u₁ u₂ + stageResidual A (k / 4) u₂ u₃) +
      ((1 / 2 : ℂ) • A (internalMeanDefect u₀ u₁ u₂ u₃) +
        B (internalMeanDefect u₀ u₁ u₂ u₃)) := by
  have hkC : (k : ℂ) ≠ 0 := fun h => hk (Complex.ofReal_eq_zero.mp h)
  have h := congrArg (fun z : E => (k : ℂ)⁻¹ • z)
    (ordered_stage_midpoint_defect A B k u₀ u₁ u₂ u₃)
  simpa only [quadraticMidpointDefect, quadraticVelocity, quadraticMean, endpointMean,
    smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hkC, inv_mul_cancel_left₀ hkC, one_smul,
    div_eq_mul_inv, mul_comm] using h

theorem quadraticSlab_gridResidual_eq_stageResiduals (A B : E →L[ℂ] E)
    (k : ℝ) (hk : k ≠ 0) (u₀ u₁ u₂ u₃ : E) (t₀ t : ℝ) :
    Complex.I • deriv (quadraticSlab (A + B) u₀ u₃ t₀ k) t -
        (A + B) (quadraticSlab (A + B) u₀ u₃ t₀ k t) =
      ((Complex.I / (k : ℂ)) • (stageResidual A (k / 4) u₀ u₁ +
        stageResidual B (k / 2) u₁ u₂ + stageResidual A (k / 4) u₂ u₃) +
        ((1 / 2 : ℂ) • A (internalMeanDefect u₀ u₁ u₂ u₃) +
          B (internalMeanDefect u₀ u₁ u₂ u₃))) +
      quadraticCorrection t₀ k t • (A + B) ((A + B) (quadraticVelocity u₀ u₃ k)) := by
  rw [quadraticSlab_gridResidual]
  change quadraticMidpointDefect (A + B) u₀ u₃ k + _ = _
  rw [quadraticMidpointDefect_eq_stageResiduals A B k hk u₀ u₁ u₂ u₃]

section ActualCayley
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_cayley_quadraticMidpointDefect (A B : Matrix ι ι ℂ)
    (k : ℝ) (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    let u₁ := step (k / 4) A u₀
    let u₂ := step (k / 2) B u₁
    let u₃ := step (k / 4) A u₂
    quadraticMidpointDefect (op A + op B) u₀ u₃ k =
      (1 / 2 : ℂ) • op A (internalMeanDefect u₀ u₁ u₂ u₃) +
        op B (internalMeanDefect u₀ u₁ u₂ u₃) := by
  dsimp only
  have h := quadraticMidpointDefect_eq_stageResiduals (op A) (op B) k hk u₀
    (step (k / 4) A u₀) (step (k / 2) B (step (k / 4) A u₀))
    (step (k / 4) A (step (k / 2) B (step (k / 4) A u₀)))
  simpa only [stageResidual_actual_cayley_zero A (k / 4) hA,
    stageResidual_actual_cayley_zero B (k / 2) hB, add_zero, smul_zero, zero_add] using h

theorem actual_cayley_quadraticSlab_gridResidual (A B : Matrix ι ι ℂ)
    (k : ℝ) (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u₀ : Vec ι) (t₀ t : ℝ) :
    let u₁ := step (k / 4) A u₀
    let u₂ := step (k / 2) B u₁
    let u₃ := step (k / 4) A u₂
    Complex.I • deriv (quadraticSlab (op A + op B) u₀ u₃ t₀ k) t -
        (op A + op B) (quadraticSlab (op A + op B) u₀ u₃ t₀ k t) =
      ((1 / 2 : ℂ) • op A (internalMeanDefect u₀ u₁ u₂ u₃) +
        op B (internalMeanDefect u₀ u₁ u₂ u₃)) +
      quadraticCorrection t₀ k t •
        (op A + op B) ((op A + op B) (quadraticVelocity u₀ u₃ k)) := by
  dsimp only
  have h := quadraticSlab_gridResidual_eq_stageResiduals (op A) (op B) k hk u₀
    (step (k / 4) A u₀) (step (k / 2) B (step (k / 4) A u₀))
    (step (k / 4) A (step (k / 2) B (step (k / 4) A u₀))) t₀ t
  simpa only [stageResidual_actual_cayley_zero A (k / 4) hA,
    stageResidual_actual_cayley_zero B (k / 2) hB, add_zero, smul_zero, zero_add] using h

private theorem quadratic_bridge_step_identity (u : Vec ι) :
    step 1 (1 : Matrix ι ι ℂ) u = (-Complex.I) • u := by
  have hr : stageResidual (op (1 : Matrix ι ι ℂ)) 1 u ((-Complex.I) • u) = 0 := by
    simp only [stageResidual, map_one, ContinuousLinearMap.one_apply,
      Complex.ofReal_one, mul_one]
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  rw [stageResidual_eq_gridFactorResidual] at hr
  exact ((stage_unique 1 (1 : Matrix ι ι ℂ) Matrix.isHermitian_one
    u ((-Complex.I) • u)).mp (sub_eq_zero.mp hr)).symm

private theorem quadratic_bridge_step_zero (a : ℝ) (u : Vec ι) :
    step a (0 : Matrix ι ι ℂ) u = u := by
  have hr : stageResidual (op (0 : Matrix ι ι ℂ)) a u u = 0 := by
    simp only [stageResidual, map_zero, ContinuousLinearMap.zero_apply,
      sub_self, smul_zero, add_zero]
  rw [stageResidual_eq_gridFactorResidual] at hr
  exact ((stage_unique a (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero
    u u).mp (sub_eq_zero.mp hr)).symm

end ActualCayley

namespace CayleyControls

def scalarCayleyState : Vec (Fin 1) := WithLp.toLp 2 (fun _ => (1 : ℂ))

def scalarCayleyEndpoint : Vec (Fin 1) :=
  step ((4 : ℝ) / 4) (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (step ((4 : ℝ) / 2) (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (step ((4 : ℝ) / 4) (1 : Matrix (Fin 1) (Fin 1) ℂ) scalarCayleyState))

theorem scalarCayleyState_ne_zero : scalarCayleyState ≠ 0 := by
  intro h
  have h₀ := congrArg (fun z : Vec (Fin 1) => z 0) h
  change (1 : ℂ) = 0 at h₀
  exact one_ne_zero h₀

theorem scalarCayleyEndpoint_eq : scalarCayleyEndpoint = -scalarCayleyState := by
  have hk : (4 : ℝ) / 4 = 1 := by norm_num
  rw [scalarCayleyEndpoint, hk, quadratic_bridge_step_zero,
    quadratic_bridge_step_identity, quadratic_bridge_step_identity, smul_smul]
  have hI : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
  rw [hI, neg_one_smul]

theorem scalarCayley_stageResiduals_zero :
    let A : Matrix (Fin 1) (Fin 1) ℂ := 1
    let B : Matrix (Fin 1) (Fin 1) ℂ := 0
    let u₁ := step ((4 : ℝ) / 4) A scalarCayleyState
    let u₂ := step ((4 : ℝ) / 2) B u₁
    stageResidual (op A) ((4 : ℝ) / 4) scalarCayleyState u₁ = 0 ∧
      stageResidual (op B) ((4 : ℝ) / 2) u₁ u₂ = 0 ∧
      stageResidual (op A) ((4 : ℝ) / 4) u₂ scalarCayleyEndpoint = 0 := by
  dsimp only
  exact ⟨stageResidual_actual_cayley_zero _ _ Matrix.isHermitian_one _,
    stageResidual_actual_cayley_zero _ _ Matrix.isHermitian_zero _,
    stageResidual_actual_cayley_zero _ _ Matrix.isHermitian_one _⟩

theorem scalarCayley_midpointDefect_eq :
    quadraticMidpointDefect
      (op (1 : Matrix (Fin 1) (Fin 1) ℂ) + op (0 : Matrix (Fin 1) (Fin 1) ℂ))
      scalarCayleyState scalarCayleyEndpoint 4 =
        (-Complex.I / 2) • scalarCayleyState := by
  rw [quadraticMidpointDefect, scalarCayleyEndpoint_eq]
  simp only [quadraticMean, quadraticVelocity, add_neg_cancel, smul_zero,
    map_zero, sub_zero]
  match_scalars <;> norm_num <;> ring

theorem scalarCayley_midpointDefect_ne_zero :
    quadraticMidpointDefect
      (op (1 : Matrix (Fin 1) (Fin 1) ℂ) + op (0 : Matrix (Fin 1) (Fin 1) ℂ))
      scalarCayleyState scalarCayleyEndpoint 4 ≠ 0 := by
  rw [scalarCayley_midpointDefect_eq]
  exact smul_ne_zero (div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num))
    scalarCayleyState_ne_zero

theorem scalarCayley_unsplitResidual_eq :
    stageResidual
      (op (1 : Matrix (Fin 1) (Fin 1) ℂ) + op (0 : Matrix (Fin 1) (Fin 1) ℂ))
      ((4 : ℝ) / 2) scalarCayleyState scalarCayleyEndpoint =
        (-2 : ℂ) • scalarCayleyState := by
  rw [stageResidual, scalarCayleyEndpoint_eq]
  simp only [neg_add_cancel, map_zero, smul_zero, add_zero]
  module

/-- Exact ordered solves do not satisfy the single unsplit CN equation. -/
theorem scalarCayley_unsplitResidual_ne_zero :
    stageResidual
      (op (1 : Matrix (Fin 1) (Fin 1) ℂ) + op (0 : Matrix (Fin 1) (Fin 1) ℂ))
      ((4 : ℝ) / 2) scalarCayleyState scalarCayleyEndpoint ≠ 0 := by
  rw [scalarCayley_unsplitResidual_eq]
  exact smul_ne_zero (by norm_num) scalarCayleyState_ne_zero

end CayleyControls
end NDEAEvolve.Exp016
