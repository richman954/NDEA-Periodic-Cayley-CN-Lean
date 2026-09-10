import StencilFourier

/-! A mesh-explicit bound for the actual centered kinetic symbol. This is the
first half of the induced A_h norm bridge: it bounds every resolved Fourier
mode, while leaving the coefficient/Parseval operator assembly explicit. -/
noncomputable section
namespace NDEAEvolve.Exp016
open NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid

theorem modeSymbol_abs_le_four_div_sq (m : ℤ) (h : ℝ) (hh : 0 < h) :
    |modeSymbol m h| ≤ 4 / h ^ 2 := by
  unfold modeSymbol
  rw [abs_div]
  have hden : 0 < h ^ 2 := sq_pos_of_pos hh
  have hc : -1 ≤ Real.cos ((m : ℝ) * h) ∧ Real.cos ((m : ℝ) * h) ≤ 1 :=
    (abs_le.mp (Real.abs_cos_le_one _))
  have hnum : 0 ≤ 2 - 2 * Real.cos ((m : ℝ) * h) := by linarith [hc.2]
  rw [abs_of_nonneg hnum]
  rw [abs_of_nonneg (le_of_lt hden)]
  apply (div_le_div_iff₀ hden hden).2
  nlinarith [hc.1]

theorem fourierCoefficient_gridKinetic_norm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) (l : Fin (2 * M + 1)) (hh : 0 < h) :
    ‖fourierCoefficient M h (op (gridKinetic (2 * M) h) y) l‖ ≤
      (4 / h ^ 2) * ‖fourierCoefficient M h y l‖ := by
  rw [fourierCoefficient_gridKinetic M h hmesh]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (modeSymbol_abs_le_four_div_sq (oddFrequency M l) h hh)
    (norm_nonneg _)

theorem gridKinetic_opNorm_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h) :
    ‖op (gridKinetic (2 * M) h)‖ ≤ 4 / h ^ 2 := by
  let K := op (gridKinetic (2 * M) h)
  let c : ℝ := 4 / h ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply ContinuousLinearMap.opNorm_le_bound K hc
  intro y
  have hcoef (l : Fin (2 * M + 1)) :=
    fourierCoefficient_gridKinetic_norm_le M h hmesh y l hh
  have hsum :
      ∑ l : Fin (2 * M + 1),
          ‖fourierCoefficient M h (K y) l‖ ^ 2 ≤
        ∑ l : Fin (2 * M + 1),
          (c * ‖fourierCoefficient M h y l‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro l _
    exact sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) |>.mpr (hcoef l)
  have hsq : ‖K y‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by
    have hout := fourierCoefficient_norm_sq M h hmesh (K y)
    have hy := fourierCoefficient_norm_sq M h hmesh y
    calc
      ‖K y‖ ^ 2 = ((2 * M + 1 : ℕ) : ℝ) *
          ∑ l : Fin (2 * M + 1), ‖fourierCoefficient M h (K y) l‖ ^ 2 := hout
      _ ≤ ((2 * M + 1 : ℕ) : ℝ) *
          ∑ l : Fin (2 * M + 1), (c * ‖fourierCoefficient M h y l‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (c * ‖y‖) ^ 2 := by
        simp only [mul_pow]
        rw [← Finset.mul_sum]
        calc
          ((2 * M + 1 : ℕ) : ℝ) * (c ^ 2 *
              ∑ i : Fin (2 * M + 1), ‖fourierCoefficient M h y i‖ ^ 2) =
            c ^ 2 * (((2 * M + 1 : ℕ) : ℝ) *
              ∑ i : Fin (2 * M + 1), ‖fourierCoefficient M h y i‖ ^ 2) := by ring
          _ = c ^ 2 * ‖y‖ ^ 2 := by rw [← hy]
  exact le_of_sq_le_sq hsq (mul_nonneg hc (norm_nonneg y))

#print axioms modeSymbol_abs_le_four_div_sq
#print axioms fourierCoefficient_gridKinetic_norm_le
#print axioms gridKinetic_opNorm_le
end NDEAEvolve.Exp016
