import QuadraticCayleyBridge

/-! Exact second-order internal-stage algebra with the A B order retained.
The first identity includes the actual denominator residuals. No commutation,
unitarity, small-step bound or matrix norm assumption enters this algebra. -/
noncomputable section
namespace NDEAEvolve.Exp016
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ordered_internalMeanDefect_residual_expansion (A B : E →L[ℂ] E)
    (k : ℝ) (u₀ u₁ u₂ u₃ : E) :
    internalMeanDefect u₀ u₁ u₂ u₃ =
      (1 / 2 : ℂ) • (stageResidual A (k / 4) u₀ u₁ - stageResidual A (k / 4) u₂ u₃) +
      (Complex.I * (k : ℂ) / 8) • A
        (stageResidual A (k / 4) u₀ u₁ + (2 : ℂ) • stageResidual B (k / 2) u₁ u₂ +
          stageResidual A (k / 4) u₂ u₃) +
      (((k ^ 2 / 32 : ℝ) : ℂ)) • A (A (u₀ + u₁ + u₂ + u₃)) +
      (((k ^ 2 / 8 : ℝ) : ℂ)) • A (B (u₁ + u₂)) := by
  simp only [stageResidual, internalMeanDefect, map_add, map_sub, map_smul,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem ordered_internalMeanDefect_exact (A B : E →L[ℂ] E)
    (k : ℝ) (u₀ u₁ u₂ u₃ : E)
    (h₁ : stageResidual A (k / 4) u₀ u₁ = 0)
    (h₂ : stageResidual B (k / 2) u₁ u₂ = 0)
    (h₃ : stageResidual A (k / 4) u₂ u₃ = 0) :
    internalMeanDefect u₀ u₁ u₂ u₃ =
      (((k ^ 2 / 32 : ℝ) : ℂ)) • A (A (u₀ + u₁ + u₂ + u₃)) +
      (((k ^ 2 / 8 : ℝ) : ℂ)) • A (B (u₁ + u₂)) := by
  simpa only [h₁, h₂, h₃, sub_self, smul_zero, map_zero, add_zero, zero_add] using
    ordered_internalMeanDefect_residual_expansion A B k u₀ u₁ u₂ u₃

/-- The normalized endpoint difference is controlled by the stage values,
without introducing a division-by-k norm loss. -/
theorem ordered_quadraticVelocity_exact (A B : E →L[ℂ] E)
    (k : ℝ) (hk : k ≠ 0) (u₀ u₁ u₂ u₃ : E)
    (h₁ : stageResidual A (k / 4) u₀ u₁ = 0)
    (h₂ : stageResidual B (k / 2) u₁ u₂ = 0)
    (h₃ : stageResidual A (k / 4) u₂ u₃ = 0) :
    quadraticVelocity u₀ u₃ k =
      (-Complex.I / 4) • A (u₀ + u₁ + u₂ + u₃) +
      (-Complex.I / 2) • B (u₁ + u₂) := by
  have he : u₃ - u₀ =
      stageResidual A (k / 4) u₀ u₁ + stageResidual B (k / 2) u₁ u₂ +
        stageResidual A (k / 4) u₂ u₃ -
      (Complex.I * (k : ℂ) / 4) • A (u₀ + u₁ + u₂ + u₃) -
      (Complex.I * (k : ℂ) / 2) • B (u₁ + u₂) := by
    simp only [stageResidual, map_add, Complex.ofReal_div, Complex.ofReal_ofNat]
    match_scalars <;> ring
  have hj : u₃ - u₀ =
      -(Complex.I * (k : ℂ) / 4) • A (u₀ + u₁ + u₂ + u₃) -
      (Complex.I * (k : ℂ) / 2) • B (u₁ + u₂) := by
    simpa only [h₁, h₂, h₃, zero_add, zero_sub, neg_smul] using he
  have hkC : (k : ℂ) ≠ 0 := fun h => hk (Complex.ofReal_eq_zero.mp h)
  rw [quadraticVelocity, hj]
  match_scalars <;> field_simp [hkC] <;> ring

#print axioms ordered_internalMeanDefect_residual_expansion
#print axioms ordered_internalMeanDefect_exact
#print axioms ordered_quadraticVelocity_exact
end NDEAEvolve.Exp016
