import SampledPotentialBounds
import CayleyPerturbation
import PotentialCutoff
import InitialSamplingBounds

/-! Actual sampled-potential trajectory stability in the physical norm.
This compares grid-time states of the ordered method. No statement here
asserts the same constant for the quadratic paths between grid times. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem sampledCayleyTrajectory_potential_perturbation (M : ℕ) (h : ℝ)
    (v w : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.HermitianFourierPotential v) (hw : Exp014.HermitianFourierPotential w)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ i : Fin (2 * M + 1), ‖Exp014.operatorPotential v ((i.val : ℝ) * h) -
      Exp014.operatorPotential w ((i.val : ℝ) * h)‖ ≤ δ)
    (y z : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ) :
    ‖sampledCayleyTrajectory M h v y k N - sampledCayleyTrajectory M h w z k N‖ ≤
      ‖y - z‖ + (∑ j ∈ Finset.range N, |k j|) * δ * ‖z‖ := by
  have hb : ‖op (sampledSplitB (2 * M) h (operatorPotentialMatrix v) -
      sampledSplitB (2 * M) h (operatorPotentialMatrix w))‖ ≤ δ := by
    apply sampledSplitB_sub_opNorm_le (2 * M) h _ _ δ hδ
    intro i
    change ‖operatorOf (operatorPotentialMatrix v ((i.val : ℝ) * h) -
      operatorPotentialMatrix w ((i.val : ℝ) * h))‖ ≤ δ
    simp only [operatorOf, map_sub]
    change ‖operatorOf (operatorPotentialMatrix v ((i.val : ℝ) * h)) -
      operatorOf (operatorPotentialMatrix w ((i.val : ℝ) * h))‖ ≤ δ
    rw [operatorPotentialMatrix_represents, operatorPotentialMatrix_represents]
    exact hd i
  exact (actualCayleyTrajectory_potential_perturbation _ _ _
    (sampledSplitA_isHermitian (2 * M) h)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h v hv)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h w hw) y z k N).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg fun _ _ => abs_nonneg _))
        (norm_nonneg z)))

theorem sampledCayleyTrajectory_potential_spatialL2_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v w : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.HermitianFourierPotential v) (hw : Exp014.HermitianFourierPotential w)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ i : Fin (2 * M + 1), ‖Exp014.operatorPotential v ((i.val : ℝ) * h) -
      Exp014.operatorPotential w ((i.val : ℝ) * h)‖ ≤ δ)
    (y z : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledCayleyTrajectory M h v y k N) x -
      fourierReconstruction M h (sampledCayleyTrajectory M h w z k N) x)
      b (2 * Real.pi) ≤ Real.sqrt h * ‖y - z‖ +
        (∑ j ∈ Finset.range N, |k j|) * δ * (Real.sqrt h * ‖z‖) := by
  have he : (fun x =>
      fourierReconstruction M h (sampledCayleyTrajectory M h v y k N) x -
      fourierReconstruction M h (sampledCayleyTrajectory M h w z k N) x) =
      fourierReconstruction M h (sampledCayleyTrajectory M h v y k N -
        sampledCayleyTrajectory M h w z k N) := by
    funext x
    simp only [← fourierEval_apply, map_sub]
  rw [he, fourierReconstruction_spatialL2 M h hmesh]
  exact (mul_le_mul_of_nonneg_left
    (sampledCayleyTrajectory_potential_perturbation M h v w hv hw δ hδ hd y z k N)
    (Real.sqrt_nonneg h)).trans_eq (by ring)

/-- Both runs start from the actual point samples of the same Exp014 state. -/
theorem sampledCayleyTrajectory_sampled_potential_spatialL2_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v w : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.HermitianFourierPotential v) (hw : Exp014.HermitianFourierPotential w)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ i : Fin (2 * M + 1), ‖Exp014.operatorPotential v ((i.val : ℝ) * h) -
      Exp014.operatorPotential w ((i.val : ℝ) * h)‖ ≤ δ)
    (a : Exp014.FourierState (E 2)) (k : ℕ → ℝ) (N : ℕ) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledCayleyTrajectory M h v (sampledInitialState M h a) k N) x -
      fourierReconstruction M h (sampledCayleyTrajectory M h w (sampledInitialState M h a) k N) x)
      b (2 * Real.pi) ≤ (∑ j ∈ Finset.range N, |k j|) * δ *
        (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  have hb := sampledCayleyTrajectory_potential_spatialL2_le M h hmesh v w hv hw δ hδ hd
    (sampledInitialState M h a) (sampledInitialState M h a) k N b
  simp only [sub_self, norm_zero, mul_zero, zero_add] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (sampledInitialState_weighted_norm_le_state M h hmesh a)
    (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hδ))

/-- Actual potential truncation costs only the omitted Fourier tail, uniformly in the grid. -/
theorem sampledCayleyTrajectory_cutoff_spatialL2_le_tail (M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledCayleyTrajectory M h v (sampledInitialState M h a) k N) x -
      fourierReconstruction M h (sampledCayleyTrajectory M h (potentialCutoff R v)
        (sampledInitialState M h a) k N) x) b (2 * Real.pi) ≤
      (∑ j ∈ Finset.range N, |k j|) * frequencyNormTail v R *
        (Real.sqrt (2 * Real.pi) * ‖a‖) :=
  sampledCayleyTrajectory_sampled_potential_spatialL2_le M h hmesh v (potentialCutoff R v)
    hHerm (potentialCutoff_hermitian R v hHerm) (frequencyNormTail v R)
    (frequencyNormTail_nonneg v R) (fun _ => operatorPotential_cutoff_norm_le_tail R v hv _)
    a k N b

theorem sampledCayleyTrajectory_cutoff_spatialL2_le_weighted (M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b : ℝ) :
    Exp015.spatialL2 (fun x =>
      fourierReconstruction M h (sampledCayleyTrajectory M h v (sampledInitialState M h a) k N) x -
      fourierReconstruction M h (sampledCayleyTrajectory M h (potentialCutoff R v)
        (sampledInitialState M h a) k N) x) b (2 * Real.pi) ≤
      (∑ j ∈ Finset.range N, |k j|) *
        ((∑' ell : ℤ, Exp014.weight ell * ‖v ell‖) / (1 + (R : ℝ)) ^ 2) *
        (Real.sqrt (2 * Real.pi) * ‖a‖) :=
  (sampledCayleyTrajectory_cutoff_spatialL2_le_tail M R h hmesh v hv hHerm a k N b).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (frequencyNormTail_le_weighted v (Exp014.regularPotential_absolute v hv) hv R)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (by positivity))

#print axioms sampledCayleyTrajectory_potential_perturbation
#print axioms sampledCayleyTrajectory_potential_spatialL2_le
#print axioms sampledCayleyTrajectory_sampled_potential_spatialL2_le
#print axioms sampledCayleyTrajectory_cutoff_spatialL2_le_tail
#print axioms sampledCayleyTrajectory_cutoff_spatialL2_le_weighted
end NDEAEvolve.Exp016
