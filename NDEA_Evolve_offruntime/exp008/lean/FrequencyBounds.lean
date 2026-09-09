import Exp007Foundation

/-! Frequency-dependent consistency bounds for finitely supported periodic
spinor data. The cutoff constants remain independent of the grid size. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
open NDEAEvolve.Exp007
namespace NDEAEvolve.Exp008

def modeSymbol (m : ℤ) (h : ℝ) : ℝ := (2-2*Real.cos ((m:ℝ)*h))/h^2
def Ct (M : ℕ) : ℝ := 1000*((M:ℝ)^2+2)^3
def Cs (M : ℕ) : ℝ := (M:ℝ)^4/8

theorem Ct_nonneg (M : ℕ) : 0 ≤ Ct M := by unfold Ct; positivity
theorem Cs_nonneg (M : ℕ) : 0 ≤ Cs M := by unfold Cs; positivity

@[simp] theorem modeSymbol_zero (h : ℝ) : modeSymbol 0 h = 0 := by
  simp [modeSymbol]

theorem modeSymbol_neg (m : ℤ) (h : ℝ) : modeSymbol (-m) h = modeSymbol m h := by
  simp [modeSymbol, neg_mul]

theorem modeSymbol_nonneg (m : ℤ) (h : ℝ) : 0 ≤ modeSymbol m h := by
  unfold modeSymbol
  exact div_nonneg (by linarith [Real.cos_le_one ((m:ℝ)*h)]) (sq_nonneg h)

theorem modeSymbol_le_sq (m : ℤ) (h : ℝ) : modeSymbol m h ≤ (m:ℝ)^2 := by
  by_cases hh : h = 0
  · simp [modeSymbol, hh, sq_nonneg]
  · unfold modeSymbol
    apply (div_le_iff₀ (sq_pos_of_ne_zero hh)).2
    have hc := Real.one_sub_sq_div_two_le_cos (x := (m:ℝ)*h)
    nlinarith

/-- Includes zero and negative frequencies. No division by the frequency is used. -/
theorem modeSymbol_consistency (m : ℤ) (h : ℝ) (hh : 0 < h)
    (hsmall : |(m:ℝ)| * h ≤ 1) :
    |modeSymbol m h-(m:ℝ)^2| ≤ (m:ℝ)^4*h^2/8 := by
  have hx : |(m:ℝ)*h| ≤ 1 := by
    rwa [abs_mul, abs_of_pos hh]
  have hc := Real.cos_bound (x := (m:ℝ)*h) hx
  have hab4 : |(m:ℝ)*h|^4 = (m:ℝ)^4*h^4 := by
    rw [← abs_pow, mul_pow, abs_of_nonneg (by positivity)]
  rw [hab4] at hc
  have he : modeSymbol m h-(m:ℝ)^2 =
      -2*(Real.cos ((m:ℝ)*h)-(1-((m:ℝ)*h)^2/2))/h^2 := by
    unfold modeSymbol
    field_simp
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hh)]
  norm_num
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  nlinarith [show 0 ≤ (m:ℝ)^4*h^4 by positivity]

theorem A_opNorm_le (lambda : ℝ) (hl : 0 ≤ lambda) :
    ‖operatorOf (A lambda)‖ ≤ lambda+1 := by
  have hid : ‖(1 : E 2 →L[ℂ] E 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  simp only [A, operatorOf, map_add, map_smul, map_one]
  calc
    _ ≤ ‖(lambda:ℂ) • (1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := norm_add_le _ _
    _ = lambda * ‖(1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    _ ≤ lambda*1+1 := add_le_add
      (mul_le_mul_of_nonneg_left hid hl) Z_opNorm_le_one
    _ = _ := by ring

theorem frequency_sq_le (M : ℕ) (m : ℤ) (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    (m:ℝ)^2 ≤ (M:ℝ)^2 := by
  calc
    _ = |(m:ℝ)|^2 := (sq_abs _).symm
    _ ≤ (M:ℝ)^2 := by gcongr

theorem frequency_fourth_le (M : ℕ) (m : ℤ) (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    (m:ℝ)^4 ≤ (M:ℝ)^4 := by
  have hs := frequency_sq_le M m hm
  nlinarith [sq_nonneg ((M:ℝ)^2-(m:ℝ)^2)]

theorem frequency_generator_norm_le (M : ℕ) (m : ℤ) (h : ℝ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) :
    ‖operatorOf (A (modeSymbol m h))‖ ≤ (M:ℝ)^2+1 := by
  have ha := A_opNorm_le (modeSymbol m h) (modeSymbol_nonneg m h)
  have hs := modeSymbol_le_sq m h
  have hm2 := frequency_sq_le M m hm
  linarith

/-- The time-step hypothesis depends on the fixed spectral cutoff, not mesh norms. -/
theorem frequency_local_error (M : ℕ) (m : ℤ) (h k : ℝ)
    (_hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) :
    ‖symmetricStepHat (A (modeSymbol m h)) B k -
      exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ ≤
      k*(Ct M*k^2+Cs M*h^2) := by
  have hm2 := frequency_sq_le M m hm
  have hm4 := frequency_fourth_le M m hm
  have hsmall : |(m:ℝ)| * h ≤ 1 :=
    (mul_le_mul_of_nonneg_right hm hh.le).trans hMh
  have ha := A_opNorm_le ((m:ℝ)^2) (sq_nonneg _)
  have hb := B_opNorm_le_one
  have hsum : ‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖ ≤ (M:ℝ)^2+2 := by
    linarith
  have hs : 2*|k| * (‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖) ≤ 1 := by
    rw [abs_of_nonneg hk]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hstep
  have ht := symmetric_cayley_exp_local_opNorm_le k (A ((m:ℝ)^2)) B
    (A_isHermitian _) B_isHermitian hs
  have hcube : (‖operatorOf (A ((m:ℝ)^2))‖+‖operatorOf B‖)^3 ≤
      ((M:ℝ)^2+2)^3 := by gcongr
  have htemp : ‖symmetricStepHat (A ((m:ℝ)^2)) B k-
      exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ ≤ Ct M*k^3 := by
    rw [abs_of_nonneg hk] at ht
    have hp := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 1000*k^3 by positivity)
    unfold Ct
    nlinarith
  have hspatial : |modeSymbol m h-(m:ℝ)^2| ≤ Cs M*h^2 := by
    have hc := modeSymbol_consistency m h hh hsmall
    have hp := mul_le_mul_of_nonneg_right hm4 (sq_nonneg h)
    unfold Cs
    nlinarith
  have hspace : ‖symmetricStepHat (A (modeSymbol m h)) B k-
      symmetricStepHat (A ((m:ℝ)^2)) B k‖ ≤ k*(Cs M*h^2) := by
    have hp := symmetric_perturbation_opNorm_le (modeSymbol m h) ((m:ℝ)^2) k
    rw [abs_of_nonneg hk] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left hspatial hk)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat (A (modeSymbol m h)) B k)
    (symmetricStepHat (A ((m:ℝ)^2)) B k)
    (exactStepHat (A ((m:ℝ)^2)+B) (k/2))
  nlinarith

theorem frequency_power_error (M : ℕ) (m : ℤ) (h k T : ℝ) (N : ℕ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    ‖symmetricStepHat (A (modeSymbol m h)) B k ^ N-
      exactStepHat (A ((m:ℝ)^2)+B) (k/2) ^ N‖ ≤
      T*(Ct M*k^2+Cs M*h^2) := by
  calc
    _ ≤ (N:ℝ) * ‖symmetricStepHat (A (modeSymbol m h)) B k-
        exactStepHat (A ((m:ℝ)^2)+B) (k/2)‖ :=
      unitary_pow_sub_pow_opNorm_le _ _ N
        (symmetricStepHat_mem_unitary k _ _ (A_isHermitian _) B_isHermitian)
        (exactStepHat_mem_unitary (k/2) _ ((A_isHermitian _).add B_isHermitian))
    _ ≤ (N:ℝ) * (k*(Ct M*k^2+Cs M*h^2)) :=
      mul_le_mul_of_nonneg_left
        (frequency_local_error M m h k hM hm hh hMh hk hstep) (Nat.cast_nonneg N)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right horizon
        (add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
          (mul_nonneg (Cs_nonneg M) (sq_nonneg h)))

theorem frequency_denominator_opNorm_le (M : ℕ) (m : ℤ) (h k : ℝ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) :
    ‖denominatorHat (A (modeSymbol m h)) (k/4)‖ ≤ 9/8 := by
  have hd := denominator_opNorm_le (A (modeSymbol m h)) (k/4)
  rw [abs_of_nonneg (by positivity : 0 ≤ k/4)] at hd
  have hn := frequency_generator_norm_le M m h hm
  have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ k/4 by positivity)
  nlinarith

/-- Actual numerical auxiliary stages discharge the measured Exp005 budget. -/
theorem frequency_stageResidualBudget_bound (dx : ℝ) (M : ℕ) (m : ℤ) (h k : ℝ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (v : E 2) :
    stageResidualBudget dx k (A (modeSymbol m h)) B v
      (Chat (A (modeSymbol m h)) (k/4) v)
      (Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) v))
      (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v) ≤
      Real.sqrt dx*(9/8)*k*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
  let H := A (modeSymbol m h)
  have hH : H.IsHermitian := A_isHermitian _
  have hd : ‖denominatorHat H (k/4)‖ ≤ 9/8 :=
    frequency_denominator_opNorm_le M m h k hm hk hstep
  have he : ‖exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v‖ ≤
      k*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
    rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (frequency_local_error M m h k hM hm hh hMh hk hstep) (norm_nonneg v))
  change stageResidualBudget dx k H B v (Chat H (k/4) v)
    (Chat B (k/2) (Chat H (k/4) v)) (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v) ≤ _
  simp only [stageResidualBudget, factorResidual_cayley_zero H (k/4) hH,
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add]
  rw [factorResidual_as_defect H (k/4) hH]
  change Real.sqrt dx*‖denominatorHat H (k/4)
    (exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v)‖ ≤ _
  calc
    _ ≤ Real.sqrt dx*(‖denominatorHat H (k/4)‖*
        ‖exactStepHat (A ((m:ℝ)^2)+B) (k/2) v-symmetricStepHat H B k v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt dx*((9/8)*(k*(Ct M*k^2+Cs M*h^2)*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul hd he (norm_nonneg _) (by norm_num)
    _ = _ := by ring

#print axioms modeSymbol_consistency
#print axioms frequency_local_error
#print axioms frequency_power_error
#print axioms frequency_stageResidualBudget_bound
end NDEAEvolve.Exp008
