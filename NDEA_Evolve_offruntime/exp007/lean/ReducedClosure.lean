import ReducedNoncommuting

/-! Explicit local stage residuals and finite-time reduced error. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007

theorem reduced_power_error (h k T : ℝ) (N : ℕ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) :
    ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k ^ N -
      exactStepHat (A0+B) (k/2) ^ N‖ ≤ T*(27000*k^2+h^2/8) := by
  have ht := unitary_pow_sub_pow_opNorm_le
    (symmetricStepHat (A (Exp006.spatialSymbol h)) B k)
    (exactStepHat (A0+B) (k/2)) N
    (symmetricStepHat_mem_unitary k _ _ (A_isHermitian _) B_isHermitian)
    (exactStepHat_mem_unitary (k/2) _ ((A_isHermitian 1).add B_isHermitian))
  calc
    _ ≤ (N : ℝ) * ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k -
        exactStepHat (A0+B) (k/2)‖ := ht
    _ ≤ (N : ℝ) * (k*(27000*k^2+h^2/8)) :=
      mul_le_mul_of_nonneg_left (reduced_local_error h k hh hhsmall hk hksmall)
        (Nat.cast_nonneg N)
    _ ≤ T*(27000*k^2+h^2/8) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right horizon (by positivity)

theorem reduced_power_error_apply (h k T : ℝ) (N : ℕ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (v : E 2) :
    ‖(symmetricStepHat (A (Exp006.spatialSymbol h)) B k ^ N) v -
      (exactStepHat (A0+B) (k/2) ^ N) v‖ ≤ T*(27000*k^2+h^2/8)*‖v‖ := by
  rw [← ContinuousLinearMap.sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (reduced_power_error h k T N hh hhsmall hk hksmall horizon) (norm_nonneg v))

theorem denominator_mul_cayley {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) : denominatorHat H a * Chat H a = numeratorHat H a := by
  have hc : cayleyD a H * cayleyN a H = cayleyN a H * cayleyD a H := by
    unfold cayleyD cayleyN
    noncomm_ring
  have he : cayleyD a H * cayley a H = cayleyN a H := by
    rw [cayley, ← mul_assoc, hc, mul_assoc, cayleyD_mul_cayleyR a H hH, mul_one]
  simpa only [denominatorHat, numeratorHat, Chat, operatorOf, map_mul] using
    congrArg (fun M : Mat n => operatorOf M) he

@[simp] theorem factorResidual_cayley_zero {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) (v : E n) :
    factorResidual H a v (Chat H a v) = 0 := by
  rw [factorResidual, ← ContinuousLinearMap.mul_apply, denominator_mul_cayley H a hH,
    sub_self]

theorem factorResidual_as_defect {n : ℕ} (H : Mat n) (a : ℝ)
    (hH : H.IsHermitian) (source target : E n) :
    factorResidual H a source target = denominatorHat H a (target - Chat H a source) := by
  rw [map_sub, ← ContinuousLinearMap.mul_apply, denominator_mul_cayley H a hH]
  rfl

theorem denominator_opNorm_le {n : ℕ} (H : Mat n) (a : ℝ) :
    ‖denominatorHat H a‖ ≤ 1 + |a| * ‖operatorOf H‖ := by
  simp only [denominatorHat, cayleyD, skewPart, cscalar, operatorOf, map_add,
    map_one, map_smul]
  calc
    _ ≤ ‖(1 : E n →L[ℂ] E n)‖ + ‖(Complex.I*(a : ℂ)) • operatorOf H‖ := norm_add_le _ _
    _ ≤ 1 + |a| * ‖operatorOf H‖ := by
      simp only [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact add_le_add
        (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E n)) (le_refl _)

/-- The first two auxiliary states are actual numerical stages. Their zero
residuals leave the final denominator applied to the independently bounded
complete-step defect. No stagewise cancellation is assumed. -/
theorem reduced_stageResidualBudget_bound (h k : ℝ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (v : E 2) :
    stageResidualBudget (2*Real.pi) k (A (Exp006.spatialSymbol h)) B v
      (Chat (A (Exp006.spatialSymbol h)) (k/4) v)
      (Chat B (k/2) (Chat (A (Exp006.spatialSymbol h)) (k/4) v))
      (exactStepHat (A0+B) (k/2) v) ≤
    Real.sqrt (2*Real.pi) * k * (29250*k^2+13*h^2/96) * ‖v‖ := by
  let H := A (Exp006.spatialSymbol h)
  have hH : H.IsHermitian := A_isHermitian _
  have hnorm : ‖operatorOf H‖ ≤ 2 :=
    A_opNorm_le_two _ (spatialSymbol_nonneg h) (spatialSymbol_le_one h (ne_of_gt hh))
  have hd : ‖denominatorHat H (k/4)‖ ≤ 13/12 := by
    have hr := denominator_opNorm_le H (k/4)
    rw [abs_of_nonneg (by positivity : 0 ≤ k/4)] at hr
    nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ k/4 by positivity)]
  have he : ‖exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v‖ ≤
      k*(27000*k^2+h^2/8)*‖v‖ := by
    rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (reduced_local_error h k hh hhsmall hk hksmall)
        (norm_nonneg v))
  change stageResidualBudget (2*Real.pi) k H B v
    (Chat H (k/4) v) (Chat B (k/2) (Chat H (k/4) v))
    (exactStepHat (A0+B) (k/2) v) ≤ _
  simp only [stageResidualBudget, factorResidual_cayley_zero H (k/4) hH,
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add]
  rw [factorResidual_as_defect H (k/4) hH]
  change Real.sqrt (2*Real.pi) * ‖denominatorHat H (k/4)
    (exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v)‖ ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi) * (‖denominatorHat H (k/4)‖ *
        ‖exactStepHat (A0+B) (k/2) v - symmetricStepHat H B k v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2*Real.pi) * ((13/12) * (k*(27000*k^2+h^2/8)*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul hd he (norm_nonneg _) (by norm_num)
    _ = _ := by ring

#print axioms reduced_power_error
#print axioms reduced_stageResidualBudget_bound
end NDEAEvolve.Exp007
