import WeightedSampledPotential

/-! Weighted DFT structure and the actual constant-block/kinetic Cayley factors.
Exp008's mode intertwiner is extended to arbitrary full-grid states. The
sampled B bound includes the original -Z offset. No invariant solution band
or stronger regularity assumption on the full Exp014 data class is used.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

theorem fourierWeightedNorm_zero (p M : ℕ) (h : ℝ) :
    fourierWeightedNorm p M h 0 = 0 := by
  simp only [fourierWeightedNorm, ← fourierCoefficientCLM_apply, map_zero,
    norm_zero, mul_zero, Finset.sum_const_zero]

theorem fourierWeightedNorm_add_le (p M : ℕ) (h : ℝ)
    (y z : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (y + z) ≤
      fourierWeightedNorm p M h y + fourierWeightedNorm p M h z := by
  simp only [fourierWeightedNorm, ← fourierCoefficientCLM_apply, map_add]
  calc
    _ ≤ ∑ r : Fin (2 * M + 1), frequencyWeight p (oddFrequency M r) *
        (‖fourierCoefficientCLM M h r y‖ + ‖fourierCoefficientCLM M h r z‖) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (frequencyWeight_nonneg p _)
    _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib]

theorem fourierWeightedNorm_neg (p M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (-y) = fourierWeightedNorm p M h y := by
  simp only [fourierWeightedNorm, ← fourierCoefficientCLM_apply, map_neg, norm_neg]

theorem fourierWeightedNorm_sub_le (p M : ℕ) (h : ℝ)
    (y z : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (y - z) ≤
      fourierWeightedNorm p M h y + fourierWeightedNorm p M h z := by
  simpa only [sub_eq_add_neg, fourierWeightedNorm_neg] using
    fourierWeightedNorm_add_le p M h y (-z)

theorem fourierWeightedNorm_smul (p M : ℕ) (h : ℝ) (a : ℂ)
    (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (a • y) = ‖a‖ * fourierWeightedNorm p M h y := by
  simp only [fourierWeightedNorm, ← fourierCoefficientCLM_apply, map_smul, norm_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- A proved action on each lifted mode determines the actual full-grid DFT action. -/
theorem fourierCoefficient_of_mode_intertwining (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (T : Vec (Grid (2 * M)) →L[ℂ] Vec (Grid (2 * M)))
    (F : Fin (2 * M + 1) → E 2 →L[ℂ] E 2)
    (hT : ∀ m u, T (modeLiftCLM (2 * M) h (oddFrequency M m) u) =
      modeLiftCLM (2 * M) h (oddFrequency M m) (F m u))
    (y : Vec (Grid (2 * M))) (r : Fin (2 * M + 1)) :
    fourierCoefficient M h (T y) r = F r (fourierCoefficient M h y r) := by
  classical
  rw [← fourierCoefficientCLM_apply M h r (T y)]
  calc
    _ = fourierCoefficientCLM M h r
        (T (∑ m : Fin (2 * M + 1), modeLiftCLM (2 * M) h (oddFrequency M m)
          (fourierCoefficient M h y m))) :=
      congrArg (fun z => fourierCoefficientCLM M h r (T z))
        (gridState_eq_modeLift_sum M h hmesh y)
    _ = ∑ m : Fin (2 * M + 1),
        if m = r then F m (fourierCoefficient M h y m) else 0 := by
      simp only [map_sum, hT, fourierCoefficientCLM_apply,
        fourierCoefficient_modeLift M h hmesh]
    _ = _ := by simp

theorem fourierCoefficient_potential_const (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (K : Mat 2) (y : Vec (Grid (2 * M))) (r : Fin (2 * M + 1)) :
    fourierCoefficient M h (op (potential (2 * M) K) y) r =
      operatorOf K (fourierCoefficient M h y r) :=
  fourierCoefficient_of_mode_intertwining M h hmesh (op (potential (2 * M) K))
    (fun _ => operatorOf K) (fun m u => potential_modeLift (2 * M) h (oddFrequency M m) K u) y r

/-- Actual Cayley evolution on every DFT coefficient, from sealed Exp008. -/
theorem fourierCoefficient_hamiltonian_step (M : ℕ) (h a : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (K : Mat 2) (hK : K.IsHermitian) (y : Vec (Grid (2 * M))) (r : Fin (2 * M + 1)) :
    fourierCoefficient M h (step a (hamiltonian (2 * M) h K) y) r =
      Chat ((modeSymbol (oddFrequency M r) h : ℂ) • 1 + K) a (fourierCoefficient M h y r) :=
  fourierCoefficient_of_mode_intertwining M h hmesh (step a (hamiltonian (2 * M) h K))
    (fun m => Chat ((modeSymbol (oddFrequency M m) h : ℂ) • 1 + K) a)
    (fun m u => hamiltonian_step_modeLift (2 * M) h a (oddFrequency M m) K hK hmesh u) y r

/-- The actual constant-block kinetic Cayley factor preserves every weighted DFT sum. -/
theorem fourierWeightedNorm_hamiltonian_step (p M : ℕ) (h a : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (K : Mat 2) (hK : K.IsHermitian) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (step a (hamiltonian (2 * M) h K) y) =
      fourierWeightedNorm p M h y := by
  unfold fourierWeightedNorm
  apply Finset.sum_congr rfl
  intro r _
  rw [fourierCoefficient_hamiltonian_step M h a hmesh K hK,
    cayley_preserves_norm a _ (scalar_add_isHermitian _ K hK)]

theorem fourierWeightedNorm_sampledSplitA_step (p M : ℕ) (h a : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (step a (sampledSplitA (2 * M) h) y) =
      fourierWeightedNorm p M h y :=
  fourierWeightedNorm_hamiltonian_step p M h a hmesh Exp007.Z Exp007.Z_isHermitian y

theorem fourierWeightedNorm_potential_const_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (K : Mat 2) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (op (potential (2 * M) K) y) ≤
      ‖operatorOf K‖ * fourierWeightedNorm p M h y := by
  unfold fourierWeightedNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  rw [fourierCoefficient_potential_const M h hmesh K]
  calc
    _ ≤ frequencyWeight p (oddFrequency M r) *
        (‖operatorOf K‖ * ‖fourierCoefficient M h y r‖) :=
      mul_le_mul_of_nonneg_left ((operatorOf K).le_opNorm _) (frequencyWeight_nonneg p _)
    _ = _ := by ring

theorem fourierWeightedNorm_potential_Z_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (op (potential (2 * M) Exp007.Z) y) ≤
      fourierWeightedNorm p M h y := by
  calc
    _ ≤ ‖operatorOf Exp007.Z‖ * fourierWeightedNorm p M h y :=
      fourierWeightedNorm_potential_const_le p M h hmesh Exp007.Z y
    _ ≤ 1 * fourierWeightedNorm p M h y :=
      mul_le_mul_of_nonneg_right Exp007.Z_opNorm_le_one (fourierWeightedNorm_nonneg p M h y)
    _ = _ := one_mul _

/-- The actual B operator includes -Z; its weighted constant is K_V + 1. -/
theorem fourierWeightedNorm_sampledSplitB_cutoff_le (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h
      (op (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) y) ≤
        (cutoffPotentialWeight p R v + 1) * fourierWeightedNorm p M h y := by
  simp only [sampledSplitB, sampledBlock_sub, sampledBlock_const, map_sub,
    ContinuousLinearMap.sub_apply]
  calc
    _ ≤ fourierWeightedNorm p M h
        (op (sampledBlock (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) y) +
        fourierWeightedNorm p M h (op (potential (2 * M) Exp007.Z) y) :=
      fourierWeightedNorm_sub_le p M h _ _
    _ ≤ cutoffPotentialWeight p R v * fourierWeightedNorm p M h y +
        fourierWeightedNorm p M h y :=
      add_le_add (fourierWeightedNorm_sampledPotential_cutoff_le p M R h hmesh v y)
        (fourierWeightedNorm_potential_Z_le p M h hmesh y)
    _ = _ := by ring

#print axioms fourierWeightedNorm_zero
#print axioms fourierWeightedNorm_add_le
#print axioms fourierWeightedNorm_neg
#print axioms fourierWeightedNorm_sub_le
#print axioms fourierWeightedNorm_smul
#print axioms fourierCoefficient_of_mode_intertwining
#print axioms fourierCoefficient_potential_const
#print axioms fourierCoefficient_hamiltonian_step
#print axioms fourierWeightedNorm_hamiltonian_step
#print axioms fourierWeightedNorm_sampledSplitA_step
#print axioms fourierWeightedNorm_potential_const_le
#print axioms fourierWeightedNorm_potential_Z_le
#print axioms fourierWeightedNorm_sampledSplitB_cutoff_le
end NDEAEvolve.Exp016
