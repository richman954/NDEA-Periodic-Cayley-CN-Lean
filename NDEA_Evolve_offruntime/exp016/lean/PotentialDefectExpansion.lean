import PotentialAlias

/-! Exact mode expansion of the actual sampled-potential spatial defect.
The grid-valued potential series and its synthesized image are summable by
the original regular-potential hypothesis. No Hermitian condition or spatial
smallness estimate is assumed. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

def potentialModeDiscrepancy (M : ℕ) (h : ℝ) (n : ℤ) (u : E 2) (x : ℝ) : E 2 :=
  fourierReconstruction M h (modeLiftCLM (2 * M) h n u) x - phase ((n : ℝ) * x) • u

private theorem pde_character_phase (ell m : ℤ) (x : ℝ) :
    Exp014.character x ell * phase ((m : ℝ) * x) =
      phase (((ell + m : ℤ) : ℝ) * x) := by
  have he : Exp014.character x ell = phase ((ell : ℝ) * x) := by
    unfold Exp014.character phase
    congr 1
    push_cast
    ring
  rw [he, ← phase_add]
  congr 1
  push_cast
  ring

private theorem pde_raw_terms_summable (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) (x : ℝ) :
    Summable (fun ell : ℤ => phase (((ell + m : ℤ) : ℝ) * x) • v ell u) := by
  apply ((Exp014.regularPotential_absolute v hv).mul_right ‖u‖).of_norm_bounded
  intro ell
  simp only [norm_smul, phase_norm, one_mul]
  exact (v ell).le_opNorm u

private theorem pde_synthesized_terms_summable (M : ℕ) (h : ℝ) (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) (x : ℝ) :
    Summable (fun ell : ℤ =>
      fourierReconstruction M h (modeLiftCLM (2 * M) h (ell + m) (v ell u)) x) := by
  simpa only [fourierEval_apply] using
    (potential_modeLift_terms_summable (2 * M) h m v hv u).mapL (fourierEval M h x)

/-- The discrepancy series converges before imposing a grid-normalization or
alias cutoff hypothesis. -/
theorem potentialModeDiscrepancy_summable (M : ℕ) (h : ℝ) (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) (x : ℝ) :
    Summable (fun ell : ℤ => potentialModeDiscrepancy M h (ell + m) (v ell u) x) := by
  exact (pde_synthesized_terms_summable M h m v hv u x).sub
    (pde_raw_terms_summable m v hv u x)

private theorem pde_potential_on_phase (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) (x : ℝ) :
    Exp014.operatorPotential v x (phase ((m : ℝ) * x) • u) =
      ∑' ell : ℤ, phase (((ell + m : ℤ) : ℝ) * x) • v ell u := by
  rw [Exp014.operatorPotential_apply v hv]
  apply tsum_congr
  intro ell
  rw [map_smul, smul_smul, pde_character_phase]

/-- The full spatial discrepancy contains both aliased reconstruction and
the original continuum product, summed over the actual DFT coefficients. -/
theorem sampledPotentialDefect_eq_sum_tsum (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (x : ℝ) (y : Vec (Grid (2 * M))) :
    sampledPotentialDefect M h v x y =
      ∑ m : Fin (2 * M + 1), ∑' ell : ℤ,
        potentialModeDiscrepancy M h (ell + oddFrequency M m)
          (v ell (fourierCoefficient M h y m)) x := by
  have hs : fourierReconstruction M h
      (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y) x =
        ∑ m : Fin (2 * M + 1), ∑' ell : ℤ,
          fourierReconstruction M h (modeLiftCLM (2 * M) h (ell + oddFrequency M m)
            (v ell (fourierCoefficient M h y m))) x := by
    rw [← fourierEval_apply]
    calc
      _ = fourierEval M h x (op (sampledBlock (2 * M) h (operatorPotentialMatrix v))
          (∑ m : Fin (2 * M + 1), modeLiftCLM (2 * M) h (oddFrequency M m)
            (fourierCoefficient M h y m))) :=
        congrArg (fun z => fourierEval M h x
          (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) z))
            (gridState_eq_modeLift_sum M h hmesh y)
      _ = ∑ m : Fin (2 * M + 1), fourierEval M h x
          (op (sampledBlock (2 * M) h (operatorPotentialMatrix v))
            (modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m))) := by
        simp only [map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m _
        rw [sampledPotential_on_modeLift (2 * M) h (oddFrequency M m) v hv,
          (fourierEval M h x).map_tsum
            (potential_modeLift_terms_summable (2 * M) h (oddFrequency M m) v hv _)]
        simp only [fourierEval_apply]
  have hr : Exp014.operatorPotential v x (fourierReconstruction M h y x) =
      ∑ m : Fin (2 * M + 1), ∑' ell : ℤ,
        phase (((ell + oddFrequency M m : ℤ) : ℝ) * x) •
          v ell (fourierCoefficient M h y m) := by
    change Exp014.operatorPotential v x
      (∑ m : Fin (2 * M + 1), phase ((oddFrequency M m : ℝ) * x) •
        fourierCoefficient M h y m) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    exact pde_potential_on_phase (oddFrequency M m) v hv (fourierCoefficient M h y m) x
  rw [sampledPotentialDefect_apply, hs, hr, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← (pde_synthesized_terms_summable M h (oddFrequency M m) v hv
    (fourierCoefficient M h y m) x).tsum_sub
      (pde_raw_terms_summable (oddFrequency M m) v hv (fourierCoefficient M h y m) x)]
  rfl

#print axioms potentialModeDiscrepancy_summable
#print axioms sampledPotentialDefect_eq_sum_tsum
end NDEAEvolve.Exp016
