import PotentialStability
import ContinuumPotentialStability

/-! Paired numerical and continuum comparison with a symmetric potential cutoff.
The error is defined from the actual ordered trajectory and the same original
point-sampled initial state. The cutoff solver error is retained explicitly;
finite potential support is not asserted to preserve solution support.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

section Continuum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original Fourier-state norm bounds its physical initial L2 norm. -/
theorem synth_spatialL2_le_state (a : Exp014.FourierState H) (b : ℝ) :
    Exp015.spatialL2 (Exp014.synth a) b (2 * Real.pi) ≤
      Real.sqrt (2 * Real.pi) * ‖a‖ :=
  spatialL2_le_sqrt_mul_of_pointwise _
    (continuous_iff_continuousAt.mpr fun x => (Exp014.synth_hasDerivAt a x).continuousAt)
    ‖a‖ b (2 * Real.pi) (norm_nonneg a) (by positivity) (Exp014.synth_norm_le a)

/-- The actual continuum solutions differ by at most the elapsed time times
the omitted potential tail and a bound on the original initial physical norm. -/
theorem solution_cutoff_spatialL2_le_tail (R : ℕ) (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState H) (b t : ℝ) (ht : 0 ≤ t) :
    Exp015.spatialL2 (fun x => Exp014.solution v a t x -
      Exp014.solution (potentialCutoff R v) a t x) b (2 * Real.pi) ≤
      t * frequencyNormTail v R * (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  have hb := solution_potential_spatialL2_le v (potentialCutoff R v)
    hv (potentialCutoff_regular R v) hHerm (potentialCutoff_hermitian R v hHerm)
    a a (frequencyNormTail v R) (frequencyNormTail_nonneg v R)
    (operatorPotential_cutoff_norm_le_tail R v hv) b t ht
  have hz : (fun x => Exp014.synth a x - Exp014.synth a x) = (0 : ℝ → H) :=
    funext fun _ => sub_self _
  rw [hz, Exp015.spatialL2_zero, zero_add] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (synth_spatialL2_le_state a b)
    (mul_nonneg ht (frequencyNormTail_nonneg v R)))

private theorem pet_spatialL2_sub_comm (u z : ℝ → H) (b L : ℝ) :
    Exp015.spatialL2 (fun x => u x - z x) b L =
      Exp015.spatialL2 (fun x => z x - u x) b L := by
  unfold Exp015.spatialL2
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change ‖u x - z x‖ ^ 2 = ‖z x - u x‖ ^ 2
  rw [norm_sub_rev]

end Continuum

/-- Physical error of the actual sampled-initialized ordered trajectory at a
comparison time. The grid-time specialization below uses actualCayleyTime. -/
def sampledCayleySolutionError (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (k : ℕ → ℝ) (N : ℕ) (b t : ℝ) : ℝ :=
  Exp015.spatialL2 (fun x =>
    fourierReconstruction M h
      (sampledCayleyTrajectory M h v (sampledInitialState M h a) k N) x -
        Exp014.solution v a t x) b (2 * Real.pi)

private theorem pet_reconstruction_continuous (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) : Continuous (fourierReconstruction M h y) := by
  simpa only [fourierEval_apply] using
    (fourierEval_continuous M h).clm_apply
      (show Continuous (fun _ : ℝ => y) from continuous_const)

/-- The actual original-potential solver error is controlled by the actual
cutoff-potential error plus both rigorously derived perturbation costs. -/
theorem sampledCayley_cutoff_error_transfer (M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b t : ℝ) (ht : 0 ≤ t) :
    sampledCayleySolutionError M h v a k N b t ≤
      sampledCayleySolutionError M h (potentialCutoff R v) a k N b t +
        ((∑ j ∈ Finset.range N, |k j|) + t) * frequencyNormTail v R *
          (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  let y := sampledInitialState M h a
  let p := fourierReconstruction M h (sampledCayleyTrajectory M h v y k N)
  let q := fourierReconstruction M h
    (sampledCayleyTrajectory M h (potentialCutoff R v) y k N)
  let u := Exp014.solution v a t
  let z := Exp014.solution (potentialCutoff R v) a t
  have hp : Continuous p := pet_reconstruction_continuous M h _
  have hq : Continuous q := pet_reconstruction_continuous M h _
  have hu : Continuous u := continuous_iff_continuousAt.mpr fun x =>
    (Exp014.solution_space_hasDerivAt v a t x).continuousAt
  have hz : Continuous z := continuous_iff_continuousAt.mpr fun x =>
    (Exp014.solution_space_hasDerivAt (potentialCutoff R v) a t x).continuousAt
  have hd := sampledCayleyTrajectory_cutoff_spatialL2_le_tail M R h hmesh v hv hHerm a k N b
  have hc := solution_cutoff_spatialL2_le_tail R v hv hHerm a b t ht
  rw [pet_spatialL2_sub_comm] at hc
  have hfirst := spatialL2_sub_triangle p q u b (2 * Real.pi) (by positivity) hp hq hu
  have hsecond := spatialL2_sub_triangle q z u b (2 * Real.pi) (by positivity) hq hz hu
  change Exp015.spatialL2 (fun x => p x - u x) b (2 * Real.pi) ≤
    Exp015.spatialL2 (fun x => q x - z x) b (2 * Real.pi) + _
  calc
    _ ≤ Exp015.spatialL2 (fun x => p x - q x) b (2 * Real.pi) +
        Exp015.spatialL2 (fun x => q x - u x) b (2 * Real.pi) := hfirst
    _ ≤ (∑ j ∈ Finset.range N, |k j|) * frequencyNormTail v R *
          (Real.sqrt (2 * Real.pi) * ‖a‖) +
        (Exp015.spatialL2 (fun x => q x - z x) b (2 * Real.pi) +
          t * frequencyNormTail v R * (Real.sqrt (2 * Real.pi) * ‖a‖)) :=
      add_le_add hd (hsecond.trans (add_le_add le_rfl hc))
    _ = _ := by ring

private theorem pet_actualTime_eq_sum (k : ℕ → ℝ) (N : ℕ) :
    actualCayleyTime k N = ∑ j ∈ Finset.range N, k j := by
  induction N with
  | zero => simp
  | succ N ih => rw [actualCayleyTime_succ, Finset.sum_range_succ, ih]

/-- At the actual grid time T, nonnegative steps make the total perturbation
cost exactly the bound 2*T*tail*sqrt(2π)*||a||. No cutoff solver limit is assumed. -/
theorem sampledCayley_gridTime_cutoff_error_transfer (M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b : ℝ) (hk : ∀ j < N, 0 ≤ k j) :
    sampledCayleySolutionError M h v a k N b (actualCayleyTime k N) ≤
      sampledCayleySolutionError M h (potentialCutoff R v) a k N b (actualCayleyTime k N) +
        2 * actualCayleyTime k N * frequencyNormTail v R *
          (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  have ht : 0 ≤ actualCayleyTime k N := by
    rw [pet_actualTime_eq_sum]
    exact Finset.sum_nonneg fun j hj => hk j (Finset.mem_range.mp hj)
  have habs : (∑ j ∈ Finset.range N, |k j|) = actualCayleyTime k N := by
    rw [pet_actualTime_eq_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact abs_of_nonneg (hk j (Finset.mem_range.mp hj))
  have hb := sampledCayley_cutoff_error_transfer M R h hmesh v hv hHerm a k N b
    (actualCayleyTime k N) ht
  rw [habs] at hb
  exact hb.trans_eq (by ring)

/-- The actual grid-time transfer has an explicit cutoff rate using the
existing weighted potential coefficient sum. -/
theorem sampledCayley_gridTime_cutoff_error_transfer_weighted (M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b : ℝ) (hk : ∀ j < N, 0 ≤ k j) :
    sampledCayleySolutionError M h v a k N b (actualCayleyTime k N) ≤
      sampledCayleySolutionError M h (potentialCutoff R v) a k N b (actualCayleyTime k N) +
        2 * actualCayleyTime k N *
          ((∑' ell : ℤ, Exp014.weight ell * ‖v ell‖) / (1 + (R : ℝ)) ^ 2) *
          (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  have ht : 0 ≤ actualCayleyTime k N := by
    rw [pet_actualTime_eq_sum]
    exact Finset.sum_nonneg fun j hj => hk j (Finset.mem_range.mp hj)
  apply (sampledCayley_gridTime_cutoff_error_transfer M R h hmesh v hv hHerm a k N b hk).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (frequencyNormTail_le_weighted v (Exp014.regularPotential_absolute v hv) hv R)
      (mul_nonneg (by norm_num) ht)) (by positivity))

#print axioms synth_spatialL2_le_state
#print axioms solution_cutoff_spatialL2_le_tail
#print axioms sampledCayleySolutionError
#print axioms sampledCayley_cutoff_error_transfer
#print axioms sampledCayley_gridTime_cutoff_error_transfer
#print axioms sampledCayley_gridTime_cutoff_error_transfer_weighted
end NDEAEvolve.Exp016
