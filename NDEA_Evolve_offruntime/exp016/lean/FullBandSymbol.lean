import FrequencyBounds

/-! Global consistency bound for the actual centered-stencil symbol.
The estimate applies to every integer frequency; no small-band hypothesis
or mesh-frequency relation is needed. The constant is deliberately coarse.
-/
noncomputable section
namespace NDEAEvolve.Exp016

/-- The positive discrete Laplacian symbol has a global fourth-order remainder
bound. This includes zero and negative modes and the entire resolved DFT band. -/
theorem modeSymbol_consistency_fullBand (m : ℤ) (h : ℝ) (hh : 0 < h) :
    |Exp008.modeSymbol m h - (m : ℝ) ^ 2| ≤ h ^ 2 * (m : ℝ) ^ 4 := by
  by_cases hsmall : |(m : ℝ)| * h ≤ 1
  · calc
      _ ≤ (m : ℝ) ^ 4 * h ^ 2 / 8 := Exp008.modeSymbol_consistency m h hh hsmall
      _ ≤ (m : ℝ) ^ 4 * h ^ 2 := div_le_self (by positivity) (by norm_num)
      _ = _ := mul_comm _ _
  · have hlarge : 1 < |(m : ℝ)| * h := lt_of_not_ge hsmall
    have hsq : 1 ≤ (|(m : ℝ)| * h) ^ 2 := by
      nlinarith [sq_nonneg (|(m : ℝ)| * h - 1)]
    rw [mul_pow, sq_abs] at hsq
    rw [abs_of_nonpos (sub_nonpos.mpr (Exp008.modeSymbol_le_sq m h))]
    calc
      -(Exp008.modeSymbol m h - (m : ℝ) ^ 2) ≤ (m : ℝ) ^ 2 := by
        linarith [Exp008.modeSymbol_nonneg m h]
      _ = (m : ℝ) ^ 2 * 1 := by ring
      _ ≤ (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 * h ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = h ^ 2 * (m : ℝ) ^ 4 := by ring

#print axioms modeSymbol_consistency_fullBand
end NDEAEvolve.Exp016
