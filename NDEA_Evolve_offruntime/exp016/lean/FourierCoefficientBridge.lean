import FourierNorm
import Mathlib.Analysis.Fourier.AddCircle

/-! Normalized continuum coefficients of the actual full-grid reconstruction.

Proof-pattern attribution: NavierStokes/SmoothFourierData.lean,
`NavierStokes.SmoothFourierData.unitCoeff_eq_integral`, upstream commit
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538 (Apache-2.0).
The external module is not imported. The wrapper pattern is adapted directly
to pinned Mathlib: physical period 2*pi instead of unit period, vector-valued
integration, explicit NDEA phase compatibility, and an actual finite-grid DFT
coefficient extraction consumer. No unit-period change of variables is used.
The original Apache license is retained separately by the project.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

private theorem fcb_character_compatibility (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (2 * Real.pi)) = phase (-(n : ℝ) * x) := by
  simp only [fourier_coe_apply, phase]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg,
    Complex.ofReal_intCast, Int.cast_neg]
  field_simp [hp]

section Coefficient
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def physicalFourierCoefficient (f : ℝ → H) (n : ℤ) : H :=
  fourierCoeffOn (show (0 : ℝ) < 2 * Real.pi by positivity) f n

theorem physicalFourierCoefficient_eq_integral (f : ℝ → H) (n : ℤ) :
    physicalFourierCoefficient f n =
      (2 * Real.pi)⁻¹ • ∫ x in (0 : ℝ)..2 * Real.pi, phase (-(n : ℝ) * x) • f x := by
  have hi := fourierCoeffOn_eq_integral f n
    (show (0 : ℝ) < 2 * Real.pi by positivity)
  calc
    physicalFourierCoefficient f n =
        (2 * Real.pi)⁻¹ • ∫ x in (0 : ℝ)..2 * Real.pi,
          fourier (-n) (x : AddCircle (2 * Real.pi)) • f x := by
      simpa only [physicalFourierCoefficient, fourier_coe_apply, sub_zero, one_div] using hi
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      exact congrArg (fun c : ℂ => c • f x) (fcb_character_compatibility n x)

variable [CompleteSpace H]

private theorem fcb_mode_integral (n l : ℤ) (u : H) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
      phase (-(n : ℝ) * x) • (phase ((l : ℝ) * x) • u)) =
      if l = n then (2 * Real.pi) • u else 0 := by
  have he (x : ℝ) : phase (-(n : ℝ) * x) * phase ((l : ℝ) * x) =
      phase (((l - n : ℤ) : ℝ) * x) := by
    rw [← phase_add]
    congr 1
    push_cast
    ring
  simp_rw [smul_smul, he]
  by_cases hln : l = n
  · subst l
    simp only [sub_self, Int.cast_zero, zero_mul, phase_zero, one_smul,
      intervalIntegral.integral_const, sub_zero, ite_true]
  · rw [intervalIntegral.integral_smul_const]
    have hz := phaseMode_integral_zero (l - n) (sub_ne_zero.mpr hln) 0
    simp only [zero_add] at hz
    rw [hz, zero_smul, if_neg hln]

end Coefficient

private theorem fcb_phase_continuous (n : ℤ) :
    Continuous (fun x : ℝ => phase ((n : ℝ) * x)) :=
  continuous_iff_continuousAt.mpr fun x => (Exp008.phaseMode_hasDerivAt n x).continuousAt

/-- Continuum extraction identifies exactly the retained finite frequencies. -/
theorem physicalFourierCoefficient_synthesis (M : ℕ) (a : Fin (2 * M + 1) → E 2)
    (n : ℤ) :
    physicalFourierCoefficient (fourierSynthesis M a) n =
      ∑ m : Fin (2 * M + 1), if oddFrequency M m = n then a m else 0 := by
  have hn : Continuous (fun x : ℝ => phase (-(n : ℝ) * x)) := by
    simpa only [Int.cast_neg] using fcb_phase_continuous (-n)
  rw [physicalFourierCoefficient_eq_integral]
  simp only [fourierSynthesis, Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum (fun m _ =>
    (hn.smul ((fcb_phase_continuous (oddFrequency M m)).smul continuous_const)).intervalIntegrable
      (0 : ℝ) (2 * Real.pi))]
  simp_rw [fcb_mode_integral]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : oddFrequency M m = n
  · simp only [if_pos hm, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul]
  · simp only [if_neg hm, smul_zero]

/-- Actual consumer: the normalized continuum coefficient of our reconstruction
is its computed finite-grid DFT coefficient. Mesh fidelity is proved separately. -/
theorem physicalFourierCoefficient_reconstruction (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) (m : Fin (2 * M + 1)) :
    physicalFourierCoefficient (fourierReconstruction M h y) (oddFrequency M m) =
      fourierCoefficient M h y m := by
  rw [fourierReconstruction, physicalFourierCoefficient_synthesis]
  have he (l : Fin (2 * M + 1)) : oddFrequency M l = oddFrequency M m ↔ l = m :=
    (oddFrequency_injective M).eq_iff
  simp_rw [he]
  simp

theorem physicalFourierCoefficient_reconstruction_off_band (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) (n : ℤ) (hn : n ∉ Set.range (oddFrequency M)) :
    physicalFourierCoefficient (fourierReconstruction M h y) n = 0 := by
  rw [fourierReconstruction, physicalFourierCoefficient_synthesis]
  apply Finset.sum_eq_zero
  intro m _
  exact if_neg (fun he => hn ⟨m, he⟩)

#print axioms physicalFourierCoefficient_eq_integral
#print axioms physicalFourierCoefficient_synthesis
#print axioms physicalFourierCoefficient_reconstruction
#print axioms physicalFourierCoefficient_reconstruction_off_band
end NDEAEvolve.Exp016
