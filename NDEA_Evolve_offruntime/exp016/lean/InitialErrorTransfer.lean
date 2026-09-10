import InitialWeightedCutoff
import PotentialErrorTransfer

/-! Removing the initial-data cutoff through the actual sampling and stability
interfaces. All bounds use the omitted absolute Fourier mass of the original
Exp014 datum; the datum itself acquires no additional regularity assumption.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem sampledInitialState_sub (M : ℕ) (h : ℝ)
    (a c : Exp014.FourierState (E 2)) :
    sampledInitialState M h (a - c) = sampledInitialState M h a - sampledInitialState M h c := by
  ext p
  rcases p with ⟨i, j⟩
  change Exp014.synth (a - c) ((i.val : ℝ) * h) j =
    Exp014.synth a ((i.val : ℝ) * h) j - Exp014.synth c ((i.val : ℝ) * h) j
  simp only [Exp014.synth, map_sub, PiLp.sub_apply]

theorem initialCutoffDifference_coefficientNorm_sum (S : ℕ) (a : Exp014.FourierState (E 2)) :
    (∑' ell, ‖Exp014.coefficient (a - initialStateCutoff S a) ell‖) =
      frequencyNormTail (Exp014.coefficient a) S := by
  unfold frequencyNormTail
  apply tsum_congr
  intro ell
  have hc : Exp014.coefficient (a - initialStateCutoff S a) ell =
      Exp014.coefficient a ell - Exp014.coefficient (initialStateCutoff S a) ell := by
    simp only [← Exp014.coefficientCLM_apply, map_sub]
  rw [hc, coefficient_initialStateCutoff]
  by_cases he : |(ell : ℝ)| ≤ (S : ℝ)
  · simp only [if_pos he, sub_self, norm_zero, if_neg (not_lt_of_ge he)]
  · simp only [if_neg he, sub_zero, if_pos (lt_of_not_ge he)]

theorem synth_norm_le_coefficientSum (a : Exp014.FourierState (E 2)) (x : ℝ) :
    ‖Exp014.synth a x‖ ≤ ∑' ell, ‖Exp014.coefficient a ell‖ := by
  rw [Exp014.synth_eq_tsum]
  apply tsum_of_norm_bounded (Exp014.coefficient_summable_norm a).hasSum
  intro ell
  simp only [norm_smul, Exp014.character_norm, one_mul, le_refl]

theorem synth_spatialL2_le_coefficientSum (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Exp015.spatialL2 (Exp014.synth a) b (2 * Real.pi) ≤
      Real.sqrt (2 * Real.pi) * ∑' ell, ‖Exp014.coefficient a ell‖ :=
  spatialL2_le_sqrt_mul_of_pointwise _
    (continuous_iff_continuousAt.mpr fun x => (Exp014.synth_hasDerivAt a x).continuousAt)
    _ b (2 * Real.pi) (tsum_nonneg (fun ell => norm_nonneg _)) (by positivity)
    (synth_norm_le_coefficientSum a)

theorem synth_initialCutoff_spatialL2_le_tail (S : ℕ) (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Exp015.spatialL2 (fun x => Exp014.synth a x - Exp014.synth (initialStateCutoff S a) x)
      b (2 * Real.pi) ≤ Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S := by
  have he : (fun x => Exp014.synth a x - Exp014.synth (initialStateCutoff S a) x) =
      Exp014.synth (a - initialStateCutoff S a) := by
    funext x
    simp only [Exp014.synth, map_sub]
  rw [he]
  simpa only [initialCutoffDifference_coefficientNorm_sum] using
    synth_spatialL2_le_coefficientSum (a - initialStateCutoff S a) b

theorem sampledInitialCutoff_weighted_norm_le_tail (M S : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) :
    Real.sqrt h * ‖sampledInitialState M h a - sampledInitialState M h (initialStateCutoff S a)‖ ≤
      Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S := by
  rw [← sampledInitialState_sub]
  simpa only [initialCutoffDifference_coefficientNorm_sum] using
    sampledInitialState_weighted_norm_le M h hmesh (a - initialStateCutoff S a)

theorem solution_initialCutoff_spatialL2_le_tail (S : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (b t : ℝ) (ht : 0 ≤ t) :
    Exp015.spatialL2 (fun x => Exp014.solution v a t x -
      Exp014.solution v (initialStateCutoff S a) t x) b (2 * Real.pi) ≤
      Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S := by
  have hc := solution_potential_spatialL2_le v v hv hv hHerm hHerm
    a (initialStateCutoff S a) 0 (by norm_num) (fun x => by simp) b t ht
  simp only [mul_zero, zero_mul, add_zero] at hc
  exact hc.trans (synth_initialCutoff_spatialL2_le_tail S a b)

private theorem iet_reconstruction_continuous (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) : Continuous (fourierReconstruction M h y) := by
  simpa only [fourierEval_apply] using
    (fourierEval_continuous M h).clm_apply (show Continuous (fun _ : ℝ => y) from continuous_const)

private theorem iet_spatialL2_sub_comm (u z : ℝ → E 2) (b L : ℝ) :
    Exp015.spatialL2 (fun x => u x - z x) b L =
      Exp015.spatialL2 (fun x => z x - u x) b L := by
  unfold Exp015.spatialL2
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change ‖u x - z x‖ ^ 2 = ‖z x - u x‖ ^ 2
  rw [norm_sub_rev]

/-- Actual initial-data error transfer, uniform in the grid and step sequence. -/
theorem sampledCayley_initialCutoff_error_transfer (M S : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (k : ℕ → ℝ) (N : ℕ) (b t : ℝ) (ht : 0 ≤ t) :
    sampledCayleySolutionError M h v a k N b t ≤
      sampledCayleySolutionError M h v (initialStateCutoff S a) k N b t +
        2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S := by
  let y := sampledInitialState M h a
  let yc := sampledInitialState M h (initialStateCutoff S a)
  let p := fourierReconstruction M h (sampledCayleyTrajectory M h v y k N)
  let q := fourierReconstruction M h (sampledCayleyTrajectory M h v yc k N)
  let u := Exp014.solution v a t
  let z := Exp014.solution v (initialStateCutoff S a) t
  have hp : Continuous p := iet_reconstruction_continuous M h _
  have hq : Continuous q := iet_reconstruction_continuous M h _
  have hu : Continuous u := continuous_iff_continuousAt.mpr fun x =>
    (Exp014.solution_space_hasDerivAt v a t x).continuousAt
  have hz : Continuous z := continuous_iff_continuousAt.mpr fun x =>
    (Exp014.solution_space_hasDerivAt v (initialStateCutoff S a) t x).continuousAt
  have hd := sampledCayleyTrajectory_potential_spatialL2_le M h hmesh v v hHerm hHerm
    0 (by norm_num) (fun i => by simp) y yc k N b
  simp only [mul_zero, zero_mul, add_zero] at hd
  have hn := hd.trans (sampledInitialCutoff_weighted_norm_le_tail M S h hmesh a)
  have hc := solution_initialCutoff_spatialL2_le_tail S v hv hHerm a b t ht
  rw [iet_spatialL2_sub_comm] at hc
  have hfirst := spatialL2_sub_triangle p q u b (2 * Real.pi) (by positivity) hp hq hu
  have hsecond := spatialL2_sub_triangle q z u b (2 * Real.pi) (by positivity) hq hz hu
  change Exp015.spatialL2 (fun x => p x - u x) b (2 * Real.pi) ≤
    Exp015.spatialL2 (fun x => q x - z x) b (2 * Real.pi) + _
  exact (hfirst.trans (add_le_add hn (hsecond.trans (add_le_add le_rfl hc)))).trans_eq (by ring)

#print axioms sampledInitialState_sub
#print axioms initialCutoffDifference_coefficientNorm_sum
#print axioms synth_norm_le_coefficientSum
#print axioms synth_spatialL2_le_coefficientSum
#print axioms synth_initialCutoff_spatialL2_le_tail
#print axioms sampledInitialCutoff_weighted_norm_le_tail
#print axioms solution_initialCutoff_spatialL2_le_tail
#print axioms sampledCayley_initialCutoff_error_transfer
end NDEAEvolve.Exp016
