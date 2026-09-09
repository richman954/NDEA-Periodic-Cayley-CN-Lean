import FourierCoefficientBridge
import FourierProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Physical coefficient extraction for the accepted all-mode weighted synthesis.
The integral-series interchange uses the existing absolute coefficient sum as
a constant majorant. The potential consumer uses the accepted convolution
identification and retains its original regular-potential hypothesis. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace NDEAEvolve.Exp016

private theorem wcb_character_eq_phase (m : ℤ) (x : ℝ) :
    Exp014.character x m = Exp006.phase ((m : ℝ) * x) := by
  unfold Exp014.character Exp006.phase
  congr 1
  push_cast
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem wcb_mode_integral (m : ℤ) (u : H) :
    (∫ x in (0 : ℝ)..2 * Real.pi, Exp014.character x m • u) =
      if m = 0 then (2 * Real.pi) • u else 0 := by
  by_cases hm : m = 0
  · subst m
    simp only [Exp014.character, Int.cast_zero, mul_zero, zero_mul,
      Complex.exp_zero, one_smul, intervalIntegral.integral_const, sub_zero, ite_true]
  · rw [intervalIntegral.integral_smul_const]
    have he : (fun x : ℝ => Exp014.character x m) =
        (fun x : ℝ => Exp006.phase ((m : ℝ) * x)) :=
      funext (wcb_character_eq_phase m)
    rw [he]
    have hz := phaseMode_integral_zero m hm 0
    simp only [zero_add] at hz
    rw [hz, zero_smul, if_neg hm]

/-- The physical-period continuum coefficient of the actual Exp014 synthesis
is its stored, unweighted Fourier coefficient. -/
theorem physicalFourierCoefficient_weightedSynthesis (b : Exp014.FourierState H)
    (n : ℤ) :
    physicalFourierCoefficient (Exp014.synth b) n = Exp014.coefficient b n := by
  let F : ℤ → ℝ → H := fun m x => Exp014.character x (m - n) • Exp014.coefficient b m
  have hF (m : ℤ) : Continuous (F m) :=
    (Exp014.character_continuous (m - n)).smul continuous_const
  have hnorm (m : ℤ) (x : ℝ) : ‖F m x‖ = ‖Exp014.coefficient b m‖ := by
    simp only [F, norm_smul, Exp014.character_norm, one_mul]
  have hsum (x : ℝ) : Summable (fun m => F m x) := by
    apply Summable.of_norm
    simpa only [hnorm] using Exp014.coefficient_summable_norm b
  have hi : HasSum (fun m : ℤ => ∫ x in (0 : ℝ)..2 * Real.pi, F m x)
      (∫ x in (0 : ℝ)..2 * Real.pi, ∑' m : ℤ, F m x) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ‖Exp014.coefficient b m‖)
      (fun m => (hF m).aestronglyMeasurable)
    · intro m
      exact ae_of_all _ fun x _ => (hnorm m x).le
    · exact ae_of_all _ fun _ _ => Exp014.coefficient_summable_norm b
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun x _ => (hsum x).hasSum
  have hpoint (x : ℝ) :
      Exp006.phase (-(n : ℝ) * x) • Exp014.synth b x = ∑' m : ℤ, F m x := by
    rw [Exp014.synth_eq_tsum,
      ← (Exp014.synthesis_terms_summable b x).tsum_const_smul]
    apply tsum_congr
    intro m
    have hn : Exp006.phase (-(n : ℝ) * x) = Exp014.character x (-n) := by
      simpa only [Int.cast_neg] using (wcb_character_eq_phase (-n) x).symm
    rw [hn, smul_smul, ← Exp014.character_add]
    simp only [F, sub_eq_add_neg, add_comm]
  have hm (m : ℤ) : (∫ x in (0 : ℝ)..2 * Real.pi, F m x) =
      if m = n then (2 * Real.pi) • Exp014.coefficient b m else 0 := by
    simpa only [F, sub_eq_zero] using wcb_mode_integral (m - n) (Exp014.coefficient b m)
  have he : (∫ x in (0 : ℝ)..2 * Real.pi,
      Exp006.phase (-(n : ℝ) * x) • Exp014.synth b x) =
        (2 * Real.pi) • Exp014.coefficient b n := by
    simp_rw [hpoint]
    rw [← hi.tsum_eq]
    simp_rw [hm]
    simp
  rw [physicalFourierCoefficient_eq_integral, he, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul]

/-- Coefficients of the actual pointwise potential product are the accepted
all-integer convolution, with no additional decay or Hermitian assumption. -/
theorem physicalFourierCoefficient_potentialProduct (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (b : Exp014.FourierState H) (n : ℤ) :
    physicalFourierCoefficient
      (fun x => Exp014.operatorPotential v x (Exp014.synth b x)) n =
        ∑' j, v j (Exp014.coefficient b (n - j)) := by
  have he : (fun x => Exp014.operatorPotential v x (Exp014.synth b x)) =
      Exp014.synth (Exp014.potentialConvolution v b) :=
    funext fun x => (Exp014.synth_potentialConvolution v hv b x).symm
  rw [he, physicalFourierCoefficient_weightedSynthesis,
    Exp014.coefficient_potentialConvolution v hv]

#print axioms physicalFourierCoefficient_weightedSynthesis
#print axioms physicalFourierCoefficient_potentialProduct
end NDEAEvolve.Exp016
