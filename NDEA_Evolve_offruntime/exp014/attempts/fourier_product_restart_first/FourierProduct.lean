import FourierSynthesis

/-! Fourier synthesis identifies the bounded coefficient convolution with
actual pointwise multiplication by the synthesized spatial potential. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def translateEquiv (j : ℤ) : ℤ ≃ ℤ where
  toFun m := m + j
  invFun m := m - j
  left_inv m := add_sub_cancel_right m j
  right_inv m := sub_add_cancel m j

theorem synthesis_terms_summable (b : FourierState H) (x : ℝ) :
    Summable fun m => character x m • coefficient b m := by
  apply Summable.of_norm
  simpa only [norm_smul, character_norm, one_mul] using coefficient_summable_norm b

theorem synth_potentialShift (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (x : ℝ) :
    synth (potentialShift j A b) x = character x j • A (synth b x) := by
  calc
    _ = ∑' m, character x m • A (coefficient b (m - j)) := by
      simp only [synth_eq_tsum, coefficient_potentialShift]
    _ = ∑' m, character x (m + j) • A (coefficient b m) := by
      simpa only [translateEquiv, Equiv.coe_fn_mk, add_sub_cancel_right] using
        ((translateEquiv j).tsum_eq
          (fun m => character x m • A (coefficient b (m - j)))).symm
    _ = character x j • A (synth b x) := by
      rw [synth_eq_tsum, A.map_tsum (synthesis_terms_summable b x),
        ← ((synthesis_terms_summable b x).mapL A).tsum_const_smul (character x j)]
      apply tsum_congr
      intro m
      simp only [character_add, map_smul, smul_smul, mul_comm]

theorem synth_potentialConvolution (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (b : FourierState H) (x : ℝ) :
    synth (potentialConvolution v b) x = operatorPotential v x (synth b x) := by
  have hs : Summable (fun j => potentialShift j (v j) b) :=
    (ContinuousLinearMap.apply ℂ (FourierState H) b).summable (potentialShift_summable v hv)
  change synthesisCLM x (potentialConvolution v b) = _
  rw [potentialConvolution_apply v hv, (synthesisCLM x).map_tsum hs]
  change (∑' j, synth (potentialShift j (v j) b) x) = _
  simp only [synth_potentialShift]
  exact (operatorPotential_apply v hv x (synth b x)).symm

end NDEAEvolve.Exp014
