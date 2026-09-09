import NDEAEvolve.Experiments.Exp003.ExactSplitUnsplitCayleyDefect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Experiment 003 Step 3 focused mathematical controls

The first witness shows that commutativity does not make a split Cayley step
equal the corresponding unsplit Cayley step.  The second result records that
the requested small-step counterexample to an `|alpha|` bound cannot exist:
when `|alpha| <= 1`, the verified quadratic estimate is stronger.  The final
witness gives the corrected large-step counterexample at `alpha = 10`.
-/

noncomputable section

open Matrix NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003.Step3Controls

abbrev Mat1 := Mat 1
abbrev Op1 := E 1 →L[ℂ] E 1

def oneResolvent : Mat1 :=
  !![((1 : ℂ) - Complex.I) / 2]

def twoResolvent : Mat1 :=
  !![((1 : ℂ) - 2 * Complex.I) / 5]

def localDefectValue : ℂ :=
  ((-2 : ℂ) + 4 * Complex.I) / 5

def tenthIdentity : Mat1 :=
  (1 / 10 : ℂ) • (1 : Mat1)

theorem oneResolvent_eq_cayleyR :
    oneResolvent = cayleyR 1 (1 : Mat1) := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cayleyD, skewPart, cscalar, oneResolvent,
    Matrix.mul_apply, Fin.sum_univ_one, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem twoResolvent_eq_cayleyR :
    twoResolvent = cayleyR 2 (1 : Mat1) := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cayleyD, skewPart, cscalar, twoResolvent,
    Matrix.mul_apply, Fin.sum_univ_one, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem cayley_one_identity :
    cayley 1 (1 : Mat1) = (-Complex.I) • (1 : Mat1) := by
  unfold cayley
  rw [← oneResolvent_eq_cayleyR]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cayleyN, skewPart, cscalar, oneResolvent,
    Matrix.mul_apply, Fin.sum_univ_one, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem cayley_two_identity :
    cayley 2 (1 : Mat1) =
      (((-3 : ℂ) - 4 * Complex.I) / 5) • (1 : Mat1) := by
  unfold cayley
  rw [← twoResolvent_eq_cayleyR]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [cayleyN, skewPart, cscalar, twoResolvent,
    Matrix.mul_apply, Fin.sum_univ_one, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem cayley_sum_identity :
    cayley 1 ((1 : Mat1) + 1) =
      (((-3 : ℂ) - 4 * Complex.I) / 5) • (1 : Mat1) := by
  have hs :
      skewPart 1 ((1 : Mat1) + 1) = skewPart 2 (1 : Mat1) := by
    unfold skewPart
    rw [smul_add]
    have hc : cscalar 2 = cscalar 1 + cscalar 1 := by
      unfold cscalar
      norm_num
      ring
    rw [hc, add_smul]
  calc
    cayley 1 ((1 : Mat1) + 1) = cayley 2 (1 : Mat1) := by
      unfold cayley cayleyN cayleyR cayleyD
      rw [hs]
    _ = (((-3 : ℂ) - 4 * Complex.I) / 5) • (1 : Mat1) :=
      cayley_two_identity

theorem commuting_local_defect_eq :
    cayley 1 (1 : Mat1) * cayley 1 (1 : Mat1) -
        cayley 1 ((1 : Mat1) + 1) =
      localDefectValue • (1 : Mat1) := by
  rw [cayley_one_identity, cayley_sum_identity]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [localDefectValue, Matrix.mul_apply, Fin.sum_univ_one,
    Complex.I_mul_I] <;> ring

theorem commuting_local_defect_ne_zero :
    cayley 1 (1 : Mat1) * cayley 1 (1 : Mat1) -
        cayley 1 ((1 : Mat1) + 1) ≠ 0 := by
  rw [commuting_local_defect_eq]
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
  have him := congrArg Complex.im h00
  norm_num [localDefectValue] at him

/-- Negative control A: two commuting Hermitian generators can have a nonzero
split-versus-unsplit Cayley defect. -/
theorem commutative_collapse_counterexample :
    (1 : Mat1).IsHermitian ∧
      Commute (1 : Mat1) (1 : Mat1) ∧
      cayley 1 (1 : Mat1) * cayley 1 (1 : Mat1) -
          cayley 1 ((1 : Mat1) + 1) ≠ 0 :=
  ⟨Matrix.isHermitian_one, Commute.refl _, commuting_local_defect_ne_zero⟩

/-- Pure ordered-real certificate behind the small-step impossibility result. -/
theorem quadratic_bound_implies_absolute_linear_bound_of_abs_le_one
    (α lhs aNorm bNorm : ℝ)
    (hα : |α| ≤ 1) (ha : 0 ≤ aNorm) (hb : 0 ≤ bNorm)
    (hquad : lhs ≤ 4 * α ^ 2 * aNorm * bNorm) :
    lhs ≤ 4 * |α| * aNorm * bNorm := by
  have hpow : α ^ 2 ≤ |α| := by
    calc
      α ^ 2 = |α| ^ 2 := (sq_abs α).symm
      _ ≤ |α| := by nlinarith [abs_nonneg α]
  have hab : 0 ≤ 4 * (aNorm * bNorm) := by positivity
  calc
    lhs ≤ 4 * α ^ 2 * aNorm * bNorm := hquad
    _ = (4 * (aNorm * bNorm)) * α ^ 2 := by ring
    _ ≤ (4 * (aNorm * bNorm)) * |α| :=
      mul_le_mul_of_nonneg_left hpow hab
    _ = 4 * |α| * aNorm * bNorm := by ring

/-- There is no counterexample to the proposed `|alpha|` replacement at a
small step: the Step-3 quadratic theorem entails that weaker estimate. -/
theorem absolute_linear_bound_holds_of_abs_le_one {n : ℕ}
    (α : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hα : |α| ≤ 1) :
    ‖Chat A α * Chat B α - Chat (A + B) α‖ ≤
      4 * |α| * ‖operatorOf A‖ * ‖operatorOf B‖ := by
  exact quadratic_bound_implies_absolute_linear_bound_of_abs_le_one
    α
    ‖Chat A α * Chat B α - Chat (A + B) α‖
    ‖operatorOf A‖ ‖operatorOf B‖ hα (norm_nonneg _) (norm_nonneg _)
    (cayley_split_unsplit_defect_opNorm_le α A B hA hB)

theorem tenthIdentity_hermitian : tenthIdentity.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i
  fin_cases j
  simp [tenthIdentity, Matrix.conjTranspose_apply]

theorem tenthIdentity_skewPart :
    skewPart 10 tenthIdentity = skewPart 1 (1 : Mat1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [tenthIdentity, skewPart, cscalar] <;> ring

theorem twiceTenthIdentity_skewPart :
    skewPart 10 (tenthIdentity + tenthIdentity) =
      skewPart 2 (1 : Mat1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [tenthIdentity, skewPart, cscalar] <;> ring

theorem cayley_tenthIdentity :
    cayley 10 tenthIdentity = cayley 1 (1 : Mat1) := by
  unfold cayley cayleyN cayleyR cayleyD
  rw [tenthIdentity_skewPart]

theorem cayley_twiceTenthIdentity :
    cayley 10 (tenthIdentity + tenthIdentity) = cayley 2 (1 : Mat1) := by
  unfold cayley cayleyN cayleyR cayleyD
  rw [twiceTenthIdentity_skewPart]

theorem large_step_local_defect_eq :
    cayley 10 tenthIdentity * cayley 10 tenthIdentity -
        cayley 10 (tenthIdentity + tenthIdentity) =
      localDefectValue • (1 : Mat1) := by
  rw [cayley_tenthIdentity, cayley_twiceTenthIdentity]
  simpa only [cayley_sum_identity, cayley_two_identity] using
    commuting_local_defect_eq

theorem large_step_local_defect_hat_eq :
    Chat tenthIdentity 10 * Chat tenthIdentity 10 -
        Chat (tenthIdentity + tenthIdentity) 10 =
      localDefectValue • (1 : Op1) := by
  simpa only [Chat, map_sub, map_mul, map_smul, map_one] using
    congrArg
      (fun M : Mat1 =>
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1) M)
      large_step_local_defect_eq

theorem tenthIdentity_operator_norm :
    ‖operatorOf tenthIdentity‖ = (1 / 10 : ℝ) := by
  change
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      ((1 / 10 : ℂ) • (1 : Mat1))‖ = (1 / 10 : ℝ)
  rw [map_smul, map_one, norm_smul, norm_one]
  norm_num

theorem localDefectValue_norm_gt_two_fifths :
    (2 / 5 : ℝ) < ‖localDefectValue‖ := by
  have him : localDefectValue.im ≠ 0 := by
    norm_num [localDefectValue]
  calc
    (2 / 5 : ℝ) = |localDefectValue.re| := by
      norm_num [localDefectValue]
    _ < ‖localDefectValue‖ :=
      (Complex.abs_re_lt_norm (z := localDefectValue)).2 him

/-- Corrected negative control B: the globally quantified estimate obtained by
replacing `alpha^2` with `|alpha|` is false.  A counterexample occurs at the
large step `alpha = 10`, with two Hermitian generators `(1/10) I`. -/
theorem missing_alpha_square_large_step_false :
    ¬ ‖Chat tenthIdentity 10 * Chat tenthIdentity 10 -
          Chat (tenthIdentity + tenthIdentity) 10‖ ≤
        4 * |(10 : ℝ)| * ‖operatorOf tenthIdentity‖ *
          ‖operatorOf tenthIdentity‖ := by
  rw [large_step_local_defect_hat_eq, norm_smul, norm_one,
    mul_one, tenthIdentity_operator_norm]
  norm_num
  exact localDefectValue_norm_gt_two_fifths

theorem missing_alpha_square_large_step_counterexample :
    tenthIdentity.IsHermitian ∧ tenthIdentity.IsHermitian ∧
      ¬ ‖Chat tenthIdentity 10 * Chat tenthIdentity 10 -
            Chat (tenthIdentity + tenthIdentity) 10‖ ≤
          4 * |(10 : ℝ)| * ‖operatorOf tenthIdentity‖ *
            ‖operatorOf tenthIdentity‖ :=
  ⟨tenthIdentity_hermitian, tenthIdentity_hermitian,
    missing_alpha_square_large_step_false⟩

end NDEAEvolve.Exp003.Step3Controls

#check NDEAEvolve.Exp003.Step3Controls.commutative_collapse_counterexample
#check NDEAEvolve.Exp003.Step3Controls.absolute_linear_bound_holds_of_abs_le_one
#check NDEAEvolve.Exp003.Step3Controls.missing_alpha_square_large_step_counterexample
#print axioms NDEAEvolve.Exp003.Step3Controls.commutative_collapse_counterexample
#print axioms NDEAEvolve.Exp003.Step3Controls.absolute_linear_bound_holds_of_abs_le_one
#print axioms NDEAEvolve.Exp003.Step3Controls.missing_alpha_square_large_step_counterexample
