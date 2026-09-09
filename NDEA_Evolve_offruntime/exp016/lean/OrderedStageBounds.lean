import OrderedStageAlgebra
import ActualCayleySynthesis

/-! Quantitative exact-stage bounds in the induced Euclidean operator norm.
The internal defect uses the ordered A B identity, and each actual Cayley
stage preserves the initial norm. No commutation or mesh estimate is assumed. -/
noncomputable section
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem ordered_stage_norm (A : Matrix ι ι ℂ) (a : ℝ)
    (hA : A.IsHermitian) (u : Vec ι) : ‖step a A u‖ = ‖u‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (step_mem_unitary a A hA) u

theorem orderedCayleyEndpoint_norm (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    ‖orderedCayleyEndpoint A B k u₀‖ = ‖u₀‖ := by
  rw [orderedCayleyEndpoint, ordered_stage_norm A _ hA,
    ordered_stage_norm B _ hB, ordered_stage_norm A _ hA]

private theorem ordered_stage_sums_norm (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    let u₁ := step (k / 4) A u₀
    let u₂ := step (k / 2) B u₁
    let u₃ := orderedCayleyEndpoint A B k u₀
    ‖u₀ + u₁ + u₂ + u₃‖ ≤ 4 * ‖u₀‖ ∧ ‖u₁ + u₂‖ ≤ 2 * ‖u₀‖ := by
  dsimp only
  have h₁ := ordered_stage_norm A (k / 4) hA u₀
  have h₂ : ‖step (k / 2) B (step (k / 4) A u₀)‖ = ‖u₀‖ := by
    rw [ordered_stage_norm B _ hB, h₁]
  have h₃ := orderedCayleyEndpoint_norm A B k hA hB u₀
  constructor
  · exact norm_add₄_le.trans_eq (by rw [h₁, h₂, h₃]; ring)
  · exact (norm_add_le _ _).trans_eq (by rw [h₁, h₂]; ring)

/-- The actual ordered stages realize the second-order identity; A B is
composition in that order and has not been exchanged with B A. -/
theorem orderedCayleyInternalDefect_expansion (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    let u₁ := step (k / 4) A u₀
    let u₂ := step (k / 2) B u₁
    let u₃ := orderedCayleyEndpoint A B k u₀
    orderedCayleyInternalDefect A B k u₀ =
      (((k ^ 2 / 32 : ℝ) : ℂ)) • op A (op A (u₀ + u₁ + u₂ + u₃)) +
      (((k ^ 2 / 8 : ℝ) : ℂ)) • op A (op B (u₁ + u₂)) := by
  dsimp only
  exact ordered_internalMeanDefect_exact (op A) (op B) k u₀ _ _ _
    (stageResidual_actual_cayley_zero A (k / 4) hA u₀)
    (stageResidual_actual_cayley_zero B (k / 2) hB _)
    (stageResidual_actual_cayley_zero A (k / 4) hA _)

theorem orderedCayleyInternalDefect_norm_le (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    ‖orderedCayleyInternalDefect A B k u₀‖ ≤
      (k ^ 2 / 8) * ‖op A‖ * (‖op A‖ + 2 * ‖op B‖) * ‖u₀‖ := by
  let u₁ := step (k / 4) A u₀
  let u₂ := step (k / 2) B u₁
  let u₃ := orderedCayleyEndpoint A B k u₀
  have hs := ordered_stage_sums_norm A B k hA hB u₀
  have hAA : ‖op A (op A (u₀ + u₁ + u₂ + u₃))‖ ≤
      ‖op A‖ * (‖op A‖ * (4 * ‖u₀‖)) :=
    (op A).le_opNorm_of_le ((op A).le_opNorm_of_le hs.1)
  have hAB : ‖op A (op B (u₁ + u₂))‖ ≤
      ‖op A‖ * (‖op B‖ * (2 * ‖u₀‖)) :=
    (op A).le_opNorm_of_le ((op B).le_opNorm_of_le hs.2)
  rw [orderedCayleyInternalDefect_expansion A B k hA hB u₀]
  calc
    _ ≤ (k ^ 2 / 32) * ‖op A (op A (u₀ + u₁ + u₂ + u₃))‖ +
        (k ^ 2 / 8) * ‖op A (op B (u₁ + u₂))‖ := by
      apply norm_add_le_of_le
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (k ^ 2 / 32) * (‖op A‖ * (‖op A‖ * (4 * ‖u₀‖))) +
        (k ^ 2 / 8) * (‖op A‖ * (‖op B‖ * (2 * ‖u₀‖))) :=
      add_le_add (mul_le_mul_of_nonneg_left hAA (by positivity))
        (mul_le_mul_of_nonneg_left hAB (by positivity))
    _ = _ := by ring

/-- The actual midpoint splitting defect has a quadratic step bound with
the explicit induced operator-norm coefficient. -/
theorem orderedCayleySplitDefect_norm_le (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    ‖orderedCayleySplitDefect A B k u₀‖ ≤
      (k ^ 2 / 16) * ‖op A‖ * (‖op A‖ + 2 * ‖op B‖)^2 * ‖u₀‖ := by
  let η := orderedCayleyInternalDefect A B k u₀
  have he := orderedCayleyInternalDefect_norm_le A B k hA hB u₀
  have ha := (op A).le_opNorm η
  have hb := (op B).le_opNorm η
  calc
    ‖orderedCayleySplitDefect A B k u₀‖ ≤ (1 / 2 : ℝ) * ‖op A η‖ + ‖op B η‖ := by
      simpa only [orderedCayleySplitDefect, norm_smul, norm_div, norm_one,
        Complex.norm_ofNat] using norm_add_le ((1 / 2 : ℂ) • op A η) (op B η)
    _ ≤ (‖op A‖ / 2 + ‖op B‖) * ‖η‖ := by nlinarith
    _ ≤ (‖op A‖ / 2 + ‖op B‖) *
        ((k ^ 2 / 8) * ‖op A‖ * (‖op A‖ + 2 * ‖op B‖) * ‖u₀‖) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem orderedCayley_quadraticVelocity_norm_le (A B : Matrix ι ι ℂ) (k : ℝ)
    (hk : 0 < k) (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    ‖quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k‖ ≤
      (‖op A‖ + ‖op B‖) * ‖u₀‖ := by
  let u₁ := step (k / 4) A u₀
  let u₂ := step (k / 2) B u₁
  let u₃ := orderedCayleyEndpoint A B k u₀
  have hs := ordered_stage_sums_norm A B k hA hB u₀
  have ha : ‖op A (u₀ + u₁ + u₂ + u₃)‖ ≤ ‖op A‖ * (4 * ‖u₀‖) :=
    (op A).le_opNorm_of_le hs.1
  have hb : ‖op B (u₁ + u₂)‖ ≤ ‖op B‖ * (2 * ‖u₀‖) :=
    (op B).le_opNorm_of_le hs.2
  have hv := ordered_quadraticVelocity_exact (op A) (op B) k hk.ne' u₀ u₁ u₂ u₃
    (stageResidual_actual_cayley_zero A (k / 4) hA u₀)
    (stageResidual_actual_cayley_zero B (k / 2) hB u₁)
    (stageResidual_actual_cayley_zero A (k / 4) hA u₂)
  rw [hv]
  calc
    _ ≤ (1 / 4 : ℝ) * ‖op A (u₀ + u₁ + u₂ + u₃)‖ +
        (1 / 2 : ℝ) * ‖op B (u₁ + u₂)‖ := by
      simpa only [norm_smul, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat] using
        norm_add_le ((-Complex.I / 4) • op A (u₀ + u₁ + u₂ + u₃))
          ((-Complex.I / 2) • op B (u₁ + u₂))
    _ ≤ (1 / 4 : ℝ) * (‖op A‖ * (4 * ‖u₀‖)) +
        (1 / 2 : ℝ) * (‖op B‖ * (2 * ‖u₀‖)) :=
      add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

theorem orderedCayley_second_generator_velocity_norm_le (A B : Matrix ι ι ℂ) (k : ℝ)
    (hk : 0 < k) (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    ‖(op A + op B) ((op A + op B)
      (quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k))‖ ≤
      (‖op A‖ + ‖op B‖)^3 * ‖u₀‖ := by
  have hH : ‖op A + op B‖ ≤ ‖op A‖ + ‖op B‖ := norm_add_le _ _
  have hv := orderedCayley_quadraticVelocity_norm_le A B k hk hA hB u₀
  exact ((op A + op B).le_of_opNorm_le_of_le hH
    ((op A + op B).le_of_opNorm_le_of_le hH hv)).trans_eq (by ring)

#print axioms orderedCayleyEndpoint_norm
#print axioms orderedCayleyInternalDefect_expansion
#print axioms orderedCayleyInternalDefect_norm_le
#print axioms orderedCayleySplitDefect_norm_le
#print axioms orderedCayley_quadraticVelocity_norm_le
#print axioms orderedCayley_second_generator_velocity_norm_le
end NDEAEvolve.Exp016
