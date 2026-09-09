import NDEAEvolve.Experiments.Exp003.FiniteNTelescopingGlobalBound
import Mathlib.Tactic.NormNum

/-!
# Experiment 003 Step 4 focused mathematical controls

The first witness demonstrates why the factor norms in a general telescoping
argument cannot be discarded without an isometry hypothesis.  The second
part records a necessary logical correction to the proposed `N^2` control:
an `N^2` upper estimate is weaker than the verified linear estimate when
`N >= 1`, so it cannot be refuted as an upper estimate.  A separate exact
small-error witness certifies instead that quadratic scaling need not be
sharp.
-/

noncomputable section

open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003.Step4Controls

abbrev Op1 := E 1 →L[ℂ] E 1

def scalarIdentity (z : ℂ) : Op1 :=
  z • (1 : Op1)

theorem scalarIdentity_one : scalarIdentity 1 = (1 : Op1) := by
  simp [scalarIdentity]

theorem scalarIdentity_mul (z w : ℂ) :
    scalarIdentity z * scalarIdentity w = scalarIdentity (z * w) := by
  ext x
  simp [scalarIdentity, mul_assoc]
  ring

theorem scalarIdentity_sub (z w : ℂ) :
    scalarIdentity z - scalarIdentity w = scalarIdentity (z - w) := by
  unfold scalarIdentity
  exact (sub_smul z w (1 : Op1)).symm

theorem scalarIdentity_sq (z : ℂ) :
    scalarIdentity z ^ 2 = scalarIdentity (z ^ 2) := by
  simpa only [pow_two] using scalarIdentity_mul z z

theorem scalarIdentity_norm (z : ℂ) :
    ‖scalarIdentity z‖ = ‖z‖ := by
  simp [scalarIdentity, norm_smul]

/-! ## Control A: arbitrary non-isometries can amplify a local defect -/

def twoIdentityOp : Op1 :=
  scalarIdentity 2

theorem twoIdentityOp_norm :
    ‖twoIdentityOp‖ = (2 : ℝ) := by
  rw [twoIdentityOp, scalarIdentity_norm]
  norm_num

theorem twoIdentityOp_sub_one_eq :
    twoIdentityOp - (1 : Op1) = scalarIdentity 1 := by
  calc
    twoIdentityOp - (1 : Op1) =
        scalarIdentity (2 : ℂ) - scalarIdentity (1 : ℂ) := by
      simp only [twoIdentityOp, scalarIdentity_one]
    _ = scalarIdentity ((2 : ℂ) - 1) := scalarIdentity_sub _ _
    _ = scalarIdentity 1 := by norm_num

theorem twoIdentityOp_sub_one_norm :
    ‖twoIdentityOp - (1 : Op1)‖ = (1 : ℝ) := by
  rw [twoIdentityOp_sub_one_eq, scalarIdentity_norm]
  norm_num

theorem twoIdentityOp_square_sub_one_eq :
    twoIdentityOp ^ 2 - (1 : Op1) ^ 2 = scalarIdentity 3 := by
  calc
    twoIdentityOp ^ 2 - (1 : Op1) ^ 2 =
        scalarIdentity (2 : ℂ) ^ 2 - scalarIdentity (1 : ℂ) ^ 2 := by
      simp only [twoIdentityOp, scalarIdentity_one]
    _ = scalarIdentity ((2 : ℂ) ^ 2) -
        scalarIdentity ((1 : ℂ) ^ 2) := by
      rw [scalarIdentity_sq, scalarIdentity_sq]
    _ = scalarIdentity (((2 : ℂ) ^ 2) - ((1 : ℂ) ^ 2)) :=
      scalarIdentity_sub _ _
    _ = scalarIdentity 3 := by norm_num

theorem twoIdentityOp_square_sub_one_norm :
    ‖twoIdentityOp ^ 2 - (1 : Op1) ^ 2‖ = (3 : ℝ) := by
  rw [twoIdentityOp_square_sub_one_eq, scalarIdentity_norm]
  norm_num

/-- Negative control A.  Although both scalar operators have norm at most
two, at `N = 2` the power defect has norm three while twice the one-step
defect has norm two. -/
theorem nonunitary_blowup_counterexample :
    ‖twoIdentityOp‖ ≤ (2 : ℝ) ∧
      ‖(1 : Op1)‖ ≤ (2 : ℝ) ∧
      ‖twoIdentityOp ^ 2 - (1 : Op1) ^ 2‖ = (3 : ℝ) ∧
      (2 : ℝ) * ‖twoIdentityOp - (1 : Op1)‖ = (2 : ℝ) ∧
      ¬ ‖twoIdentityOp ^ 2 - (1 : Op1) ^ 2‖ ≤
          (2 : ℝ) * ‖twoIdentityOp - (1 : Op1)‖ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [twoIdentityOp_norm]
  · rw [norm_one]
    norm_num
  · exact twoIdentityOp_square_sub_one_norm
  · rw [twoIdentityOp_sub_one_norm]
    norm_num
  · rw [twoIdentityOp_square_sub_one_norm,
      twoIdentityOp_sub_one_norm]
    norm_num

/-! ## Control B: correction and strict non-sharpness witness -/

/-- For `N >= 1` and a nonnegative local estimate, every linear-in-`N`
upper estimate entails the corresponding (weaker) quadratic-in-`N` estimate.
Thus no counterexample to the quadratic upper estimate can coexist with the
linear theorem under the same hypotheses. -/
theorem linear_bound_implies_n_squared_bound
    (N : ℕ) (x localBound : ℝ)
    (hN : (1 : ℝ) ≤ (N : ℝ))
    (hlocal : 0 ≤ localBound)
    (hlinear : x ≤ (N : ℝ) * localBound) :
    x ≤ (N : ℝ) ^ 2 * localBound := by
  have hNnonneg : 0 ≤ (N : ℝ) := le_trans (by norm_num) hN
  have hNleSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      (N : ℝ) = (N : ℝ) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hNnonneg
      _ = (N : ℝ) ^ 2 := (pow_two _).symm
  exact hlinear.trans (mul_le_mul_of_nonneg_right hNleSq hlocal)

def nineTenthsIdentityOp : Op1 :=
  scalarIdentity (9 / 10)

theorem nineTenthsIdentityOp_sub_one_eq :
    nineTenthsIdentityOp - (1 : Op1) =
      scalarIdentity (-1 / 10) := by
  calc
    nineTenthsIdentityOp - (1 : Op1) =
        scalarIdentity (9 / 10 : ℂ) - scalarIdentity (1 : ℂ) := by
      simp only [nineTenthsIdentityOp, scalarIdentity_one]
    _ = scalarIdentity ((9 / 10 : ℂ) - 1) := scalarIdentity_sub _ _
    _ = scalarIdentity (-1 / 10) := by norm_num

theorem nineTenthsIdentityOp_sub_one_norm :
    ‖nineTenthsIdentityOp - (1 : Op1)‖ = (1 / 10 : ℝ) := by
  rw [nineTenthsIdentityOp_sub_one_eq, scalarIdentity_norm]
  norm_num

theorem nineTenthsIdentityOp_square_sub_one_eq :
    nineTenthsIdentityOp ^ 2 - (1 : Op1) ^ 2 =
      scalarIdentity (-19 / 100) := by
  calc
    nineTenthsIdentityOp ^ 2 - (1 : Op1) ^ 2 =
        scalarIdentity (9 / 10 : ℂ) ^ 2 -
          scalarIdentity (1 : ℂ) ^ 2 := by
      simp only [nineTenthsIdentityOp, scalarIdentity_one]
    _ = scalarIdentity ((9 / 10 : ℂ) ^ 2) -
        scalarIdentity ((1 : ℂ) ^ 2) := by
      rw [scalarIdentity_sq, scalarIdentity_sq]
    _ = scalarIdentity (((9 / 10 : ℂ) ^ 2) - ((1 : ℂ) ^ 2)) :=
      scalarIdentity_sub _ _
    _ = scalarIdentity (-19 / 100) := by norm_num

theorem nineTenthsIdentityOp_square_sub_one_norm :
    ‖nineTenthsIdentityOp ^ 2 - (1 : Op1) ^ 2‖ =
      (19 / 100 : ℝ) := by
  rw [nineTenthsIdentityOp_square_sub_one_eq, scalarIdentity_norm]
  norm_num

/-- Corrected control B.  The one-step difference is the exact small value
`1/10`, while the two-step difference is `19/100`, strictly below the
quadratic allowance `2^2 * (1/10) = 2/5`.  This certifies non-sharpness; it
does not purport to refute the weaker quadratic upper estimate. -/
theorem n_squared_strict_slack_witness :
    ‖nineTenthsIdentityOp - (1 : Op1)‖ = (1 / 10 : ℝ) ∧
      ‖nineTenthsIdentityOp ^ 2 - (1 : Op1) ^ 2‖ =
        (19 / 100 : ℝ) ∧
      ‖nineTenthsIdentityOp ^ 2 - (1 : Op1) ^ 2‖ <
        (2 : ℝ) ^ 2 * ‖nineTenthsIdentityOp - (1 : Op1)‖ := by
  refine ⟨nineTenthsIdentityOp_sub_one_norm,
    nineTenthsIdentityOp_square_sub_one_norm, ?_⟩
  rw [nineTenthsIdentityOp_square_sub_one_norm,
    nineTenthsIdentityOp_sub_one_norm]
  norm_num

end NDEAEvolve.Exp003.Step4Controls

#check NDEAEvolve.Exp003.Step4Controls.nonunitary_blowup_counterexample
#check NDEAEvolve.Exp003.Step4Controls.linear_bound_implies_n_squared_bound
#check NDEAEvolve.Exp003.Step4Controls.n_squared_strict_slack_witness
#print axioms NDEAEvolve.Exp003.Step4Controls.nonunitary_blowup_counterexample
#print axioms NDEAEvolve.Exp003.Step4Controls.linear_bound_implies_n_squared_bound
#print axioms NDEAEvolve.Exp003.Step4Controls.n_squared_strict_slack_witness
