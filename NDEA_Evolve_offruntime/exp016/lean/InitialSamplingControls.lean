import InitialSamplingBounds
import OneNodeCosine

/-! Exact resolved initialization and an actual unresolved-mode control.
The latter uses a nonzero Exp014 Fourier state supported at +1. Its one-node
samples reconstruct a constant, while its original synthesized field oscillates.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

private theorem isc_tail_zero (M : ℕ) (a : Exp014.FourierState (E 2))
    (ha : ∀ ell : ℤ, (M : ℝ) < |(ell : ℝ)| → Exp014.coefficient a ell = 0) :
    frequencyNormTail (Exp014.coefficient a) M = 0 := by
  unfold frequencyNormTail
  have hz (ell : ℤ) :
      (if (M : ℝ) < |(ell : ℝ)| then ‖Exp014.coefficient a ell‖ else 0) = 0 := by
    by_cases he : (M : ℝ) < |(ell : ℝ)|
    · rw [if_pos he, ha ell he, norm_zero]
    · exact if_neg he
  simp only [hz, tsum_zero]

/-- Actual initialization is exact when the inclusive Fourier support is resolved. -/
theorem sampledInitialState_exact_of_resolved_support (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2))
    (ha : ∀ ell : ℤ, (M : ℝ) < |(ell : ℝ)| → Exp014.coefficient a ell = 0)
    (x : ℝ) :
    fourierReconstruction M h (sampledInitialState M h a) x = Exp014.synth a x := by
  have hn := sampledInitialState_error_norm_le_tail M M le_rfl h hmesh a x
  rw [isc_tail_zero M a ha, mul_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

namespace Controls

private def isc_coefficients (ell : ℤ) : E 2 :=
  if ell = 1 then OneNodeCosine.spinor else 0

private theorem isc_coefficients_regular :
    Summable (fun ell : ℤ => Exp014.weight ell * ‖isc_coefficients ell‖) := by
  have he : (fun ell : ℤ => Exp014.weight ell * ‖isc_coefficients ell‖) =
      (fun ell : ℤ => if ell = 1 then Exp014.weight 1 * ‖OneNodeCosine.spinor‖ else 0) := by
    funext ell
    by_cases hell : ell = 1 <;> simp [isc_coefficients, hell]
  rw [he]
  exact (hasSum_ite_eq 1 _).summable

/-- The genuine weighted Fourier state with the nonzero spinor at frequency +1. -/
def unresolvedModeOneState : Exp014.FourierState (E 2) :=
  Exp014.ofCoefficients isc_coefficients isc_coefficients_regular

private theorem isc_character_phase (ell : ℤ) (x : ℝ) :
    Exp014.character x ell = phase ((ell : ℝ) * x) := by
  unfold Exp014.character phase
  congr 1
  push_cast
  ring

private theorem isc_synth (x : ℝ) :
    Exp014.synth unresolvedModeOneState x = phase x • OneNodeCosine.spinor := by
  rw [Exp014.synth_eq_tsum]
  simp only [unresolvedModeOneState, Exp014.coefficient_ofCoefficients]
  rw [tsum_eq_single 1]
  · simp [isc_coefficients, isc_character_phase]
  · intro ell hell
    simp [isc_coefficients, hell]

private theorem isc_samples (h : ℝ) :
    sampledInitialState 0 h unresolvedModeOneState =
      modeLiftCLM 0 h 1 OneNodeCosine.spinor := by
  rw [sampledInitialState_eq_tsum]
  simp only [unresolvedModeOneState, Exp014.coefficient_ofCoefficients]
  rw [tsum_eq_single 1]
  · simp [isc_coefficients]
  · intro ell hell
    rw [show isc_coefficients ell = 0 from if_neg hell]
    exact (modeLiftCLM (2 * 0) h ell).map_zero

/-- The actual one-node initialization aliases a nonzero +1 mode to a constant.
Both formulas concern the same Exp014 initial state and the existing sampler. -/
theorem unresolved_mode_one_initialization (x : ℝ) :
    Exp014.synth unresolvedModeOneState x = phase x • OneNodeCosine.spinor ∧
    fourierReconstruction 0 (2 * Real.pi)
      (sampledInitialState 0 (2 * Real.pi) unresolvedModeOneState) x = OneNodeCosine.spinor := by
  refine ⟨isc_synth x, ?_⟩
  rw [isc_samples]
  simpa [oddFrequency, phase] using
    fourierReconstruction_modeLift_alias_frequency 0 (2 * Real.pi) (by norm_num)
      1 (0 : Fin 1) (by norm_num [oddFrequency]) OneNodeCosine.spinor x

end Controls

#print axioms sampledInitialState_exact_of_resolved_support
#print axioms Controls.unresolvedModeOneState
#print axioms Controls.unresolved_mode_one_initialization
end NDEAEvolve.Exp016
