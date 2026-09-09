import PotentialDefectExpansion

/-! The actual existing point-sampling map applied to the Exp014 initial field.
Both the sampled grid series and its reconstruction discrepancy are convergent
series of the original Fourier coefficients. No band truncation, alternative
sampling rule, or initialization-error hypothesis is introduced. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

/-- Point samples of the original initial field using the existing grid map. -/
def sampledInitialState (M : ℕ) (h : ℝ) (a : Exp014.FourierState (E 2)) :
    Vec (Grid (2 * M)) :=
  Exp010.sampleSolution (2 * M) h (fun _ => Exp014.synth a) 0

private theorem se_modeLift_norm (n : ℕ) (h : ℝ) (ell : ℤ) (u : E 2) :
    ‖modeLiftCLM n h ell u‖ = Real.sqrt ((n + 1 : ℕ) : ℝ) * ‖u‖ := by
  rw [modeLiftCLM_apply, ← Real.sqrt_sq (norm_nonneg (modeLift n h ell u)),
    modeLift_norm_sq, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg u)]

private theorem se_character_phase (ell : ℤ) (x : ℝ) :
    Exp014.character x ell = phase ((ell : ℝ) * x) := by
  unfold Exp014.character phase
  congr 1
  push_cast
  ring

private theorem se_synth_eq_tsum (a : Exp014.FourierState (E 2)) (x : ℝ) :
    Exp014.synth a x = ∑' ell : ℤ, phase ((ell : ℝ) * x) • Exp014.coefficient a ell := by
  rw [Exp014.synth_eq_tsum]
  exact tsum_congr fun ell => congrArg (fun c : ℂ => c • Exp014.coefficient a ell)
    (se_character_phase ell x)

private theorem se_node_modeLift (n : ℕ) (h : ℝ) (ell : ℤ) (u : E 2)
    (i : Fin (n + 1)) :
    Exp011.nodeValue n (modeLiftCLM n h ell u) i =
      phase ((ell : ℝ) * ((i.val : ℝ) * h)) • u := by
  ext b
  rfl

/-- Absolute coefficient summability controls the complete sampled grid series. -/
theorem initial_modeLift_terms_summable (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) :
    Summable (fun ell : ℤ => modeLiftCLM (2 * M) h ell (Exp014.coefficient a ell)) := by
  apply ((Exp014.coefficient_summable_norm a).mul_left
    (Real.sqrt ((2 * M + 1 : ℕ) : ℝ))).of_norm_bounded
  intro ell
  exact (se_modeLift_norm (2 * M) h ell (Exp014.coefficient a ell)).le

/-- The original point samples are exactly the sum of all sampled Fourier modes. -/
theorem sampledInitialState_eq_tsum (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) :
    sampledInitialState M h a =
      ∑' ell : ℤ, modeLiftCLM (2 * M) h ell (Exp014.coefficient a ell) := by
  have he (i : Fin (2 * M + 1)) :
      Exp011.nodeValue (2 * M) (sampledInitialState M h a) i =
        Exp011.nodeValue (2 * M)
          (∑' ell : ℤ, modeLiftCLM (2 * M) h ell (Exp014.coefficient a ell)) i := by
    have hr := (nodeValueCLM (2 * M) i).map_tsum (initial_modeLift_terms_summable M h a)
    simp only [nodeValueCLM_apply, se_node_modeLift] at hr
    rw [sampledInitialState, Exp011.nodeValue_sampleSolution]
    exact (se_synth_eq_tsum a ((i.val : ℝ) * h)).trans hr.symm
  ext p
  rcases p with ⟨i, b⟩
  exact congrArg (fun z : E 2 => z b) (he i)

private theorem se_raw_terms_summable (a : Exp014.FourierState (E 2)) (x : ℝ) :
    Summable (fun ell : ℤ => phase ((ell : ℝ) * x) • Exp014.coefficient a ell) := by
  apply Summable.of_norm
  simpa only [norm_smul, phase_norm, one_mul] using Exp014.coefficient_summable_norm a

private theorem se_reconstructed_terms_summable (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    Summable (fun ell : ℤ => fourierReconstruction M h
      (modeLiftCLM (2 * M) h ell (Exp014.coefficient a ell)) x) := by
  simpa only [fourierEval_apply] using
    (initial_modeLift_terms_summable M h a).mapL (fourierEval M h x)

/-- The exact interpolation-error series converges without imposing a mesh
normalization or an assumed tail estimate. -/
theorem initial_discrepancy_terms_summable (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    Summable (fun ell : ℤ => potentialModeDiscrepancy M h ell (Exp014.coefficient a ell) x) :=
  (se_reconstructed_terms_summable M h a x).sub (se_raw_terms_summable a x)

/-- Reconstruction commutes with the absolutely convergent sampled series. -/
theorem sampledInitialState_reconstruction_eq_tsum (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    fourierReconstruction M h (sampledInitialState M h a) x =
      ∑' ell : ℤ, fourierReconstruction M h
        (modeLiftCLM (2 * M) h ell (Exp014.coefficient a ell)) x := by
  rw [← fourierEval_apply M h x (sampledInitialState M h a), sampledInitialState_eq_tsum,
    (fourierEval M h x).map_tsum (initial_modeLift_terms_summable M h a)]
  exact tsum_congr fun ell => fourierEval_apply M h x _

/-- The actual initialized reconstruction minus the original field is the
sum of all mode discrepancies, including continuum frequencies beyond the grid. -/
theorem sampledInitialState_reconstruction_sub_synth (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) (x : ℝ) :
    fourierReconstruction M h (sampledInitialState M h a) x - Exp014.synth a x =
      ∑' ell : ℤ, potentialModeDiscrepancy M h ell (Exp014.coefficient a ell) x := by
  rw [sampledInitialState_reconstruction_eq_tsum, se_synth_eq_tsum,
    ← (se_reconstructed_terms_summable M h a x).tsum_sub (se_raw_terms_summable a x)]
  rfl

#print axioms initial_modeLift_terms_summable
#print axioms sampledInitialState_eq_tsum
#print axioms initial_discrepancy_terms_summable
#print axioms sampledInitialState_reconstruction_eq_tsum
#print axioms sampledInitialState_reconstruction_sub_synth
end NDEAEvolve.Exp016
