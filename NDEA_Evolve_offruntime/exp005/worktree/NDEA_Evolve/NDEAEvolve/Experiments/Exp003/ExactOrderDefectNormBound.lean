import NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction

noncomputable section
open NDEAEvolve.Exp002
namespace NDEAEvolve.Exp003

abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Rhat {n : ℕ} (X : Mat n) (γ : ℝ) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR γ X)
abbrev Chat {n : ℕ} (X : Mat n) (γ : ℝ) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley γ X)
abbrev operatorOf {n : ℕ} (X : Mat n) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) X

private theorem cayley_order_defect_CLM {n : ℕ}
    (α β : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Chat A α * Chat B β - Chat B β * Chat A α =
      (-4 * (α : ℂ) * (β : ℂ)) •
        (Rhat A α * Rhat B β *
          (operatorOf A * operatorOf B - operatorOf B * operatorOf A) *
          Rhat B β * Rhat A α) := by
  simpa only [NDEAEvolve.Exp002.commutator, map_mul, map_sub, map_smul] using
    congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayley_order_defect α β A B
        (cayleyD_mul_cayleyR α A hA) (cayleyR_mul_cayleyD α A hA)
        (cayleyD_mul_cayleyR β B hB) (cayleyR_mul_cayleyD β B hB))

/-- The exact order-defect bound in the induced Euclidean operator norm. -/
theorem cayley_order_defect_opNorm_le {n : ℕ}
    (α β : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Chat A α * Chat B β - Chat B β * Chat A α‖ ≤
      4 * |α * β| *
        ‖operatorOf A * operatorOf B - operatorOf B * operatorOf A‖ := by
  let K := operatorOf A * operatorOf B - operatorOf B * operatorOf A
  rw [cayley_order_defect_CLM α β A B hA hB, norm_smul]
  have hs : ‖(-4 * (α : ℂ) * (β : ℂ))‖ = 4 * |α * β| := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_mul]
    ring
  rw [hs]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (abs_nonneg _))
  have hRα : ‖Rhat A α‖ ≤ 1 := cayleyR_toEuclideanCLM_opNorm_le_one α A hA
  have hRβ : ‖Rhat B β‖ ≤ 1 := cayleyR_toEuclideanCLM_opNorm_le_one β B hB
  change ‖Rhat A α * Rhat B β * K * Rhat B β * Rhat A α‖ ≤ ‖K‖
  calc
    ‖Rhat A α * Rhat B β * K * Rhat B β * Rhat A α‖
        ≤ ‖Rhat A α * Rhat B β * K * Rhat B β‖ * ‖Rhat A α‖ := norm_mul_le _ _
    _ ≤ ‖Rhat A α * Rhat B β * K * Rhat B β‖ := by
      simpa using mul_le_mul_of_nonneg_left hRα (norm_nonneg _)
    _ ≤ ‖Rhat A α * Rhat B β * K‖ * ‖Rhat B β‖ := norm_mul_le _ _
    _ ≤ ‖Rhat A α * Rhat B β * K‖ := by
      simpa using mul_le_mul_of_nonneg_left hRβ (norm_nonneg _)
    _ ≤ ‖Rhat A α * Rhat B β‖ * ‖K‖ := norm_mul_le _ _
    _ ≤ (‖Rhat A α‖ * ‖Rhat B β‖) * ‖K‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * 1) * ‖K‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hRα hRβ (norm_nonneg _) zero_le_one) (norm_nonneg _)
    _ = ‖K‖ := by ring

end NDEAEvolve.Exp003

#check @NDEAEvolve.Exp003.cayley_order_defect_opNorm_le
#print axioms NDEAEvolve.Exp003.cayley_order_defect_opNorm_le
