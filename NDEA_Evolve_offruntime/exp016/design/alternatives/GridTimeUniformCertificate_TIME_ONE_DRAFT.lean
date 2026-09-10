import SmoothCutoffConvergence

/-! Preserved unverified time-1 draft; the active next route uses every fixed T.
A common explicit certificate for every grid-time prefix of the saved
time-1 schedule. Prefix sums are bounded by the complete nonnegative budgets;
the actual comparison time remains actualCayleyTime for each prefix.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem sampledSpatialStageBudget_nonneg (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 ≤ k) :
    0 ≤ sampledSpatialStageBudget M h v y b k := by
  have hb (z : Vec (Grid (2 * M))) : 0 ≤ sampledSpatialDefectBudget M h v z b :=
    add_nonneg (Exp015.spatialL2_nonneg _ _ _) (Exp015.spatialL2_nonneg _ _ _)
  dsimp only [sampledSpatialStageBudget]
  exact add_nonneg (add_nonneg (hb _) (mul_nonneg (by positivity) (hb _)))
    (mul_nonneg (by positivity) (hb _))

/-- Every prefix of the original ordered trajectory uses the same vanishing budget. -/
theorem scheduledCayley_gridTime_error_le (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (q N : ℕ) (hN : N ≤ temporalStepCount q) :
    sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
      (fun _ => temporalStepSize q) N b (actualCayleyTime (fun _ => temporalStepSize q) N) ≤
        scheduledInitialError a b q + scheduledTemporalBound v a q + scheduledSpatialSum v a b q := by
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := temporalStepSize q
  let y := sampledInitialState M h a
  have hk : 0 < k := temporalStepSize_pos q
  have he := sampledCayley_gridTime_explicitTemporal_error M h (temporalSchedule_mesh q)
    (temporalSchedule_mesh_pos q) v hv hHerm a y b (fun _ => k) N (fun _ _ => hk)
  have hcube : (∑ _j ∈ Finset.range N, k^3) ≤ k^2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (temporalStepCount q), k^3 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (fun _ _ _ => by positivity)
      _ = _ := temporalSchedule_sum_cube q
  have hs : (∑ j ∈ Finset.range N, k * sampledSpatialStageBudget M h v
      (sampledCayleyTrajectory M h v y (fun _ => k) j) b k) ≤ scheduledSpatialSum v a b q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
    intro j _ _
    exact mul_nonneg hk.le (sampledSpatialStageBudget_nonneg M h v _ b k hk.le)
  have ht : (Real.sqrt h * ‖y‖) * physicalTemporalCoefficient h v *
      (∑ _j ∈ Finset.range N, k^3) ≤ scheduledTemporalBound v a q := by
    calc
      _ ≤ (Real.sqrt h * ‖y‖) * physicalTemporalCoefficient h v * k^2 :=
        mul_le_mul_of_nonneg_left hcube
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
            (physicalTemporalCoefficient_nonneg h v))
      _ ≤ (Real.sqrt (2 * Real.pi) * ‖a‖) * physicalTemporalCoefficient h v * k^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (sampledInitialState_weighted_norm_le_state M h (temporalSchedule_mesh q) a)
            (physicalTemporalCoefficient_nonneg h v)) (sq_nonneg k)
      _ = _ := by unfold scheduledTemporalBound; dsimp only [h, k]; ring
  have hf := he.trans (add_le_add (add_le_add le_rfl ht) hs)
  simpa only [sampledCayleySolutionError, ← fourierReconstruction_eq_independentTarget,
    scheduledInitialError] using hf

theorem temporalSchedule_prefix_time (q N : ℕ) :
    actualCayleyTime (fun _ => temporalStepSize q) N = (N : ℝ) * temporalStepSize q := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [actualCayleyTime_succ, ih]
    push_cast
    ring

theorem temporalSchedule_prefix_time_mem (q N : ℕ) (hN : N ≤ temporalStepCount q) :
    actualCayleyTime (fun _ => temporalStepSize q) N ∈ Set.Icc (0 : ℝ) 1 := by
  rw [temporalSchedule_prefix_time]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg N) (temporalStepSize_pos q).le
  · calc
      _ ≤ (temporalStepCount q : ℝ) * temporalStepSize q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (temporalStepSize_pos q).le
      _ = 1 := by rw [← temporalSchedule_prefix_time, temporalSchedule_time_one]

#print axioms sampledSpatialStageBudget_nonneg
#print axioms scheduledCayley_gridTime_error_le
#print axioms temporalSchedule_prefix_time
#print axioms temporalSchedule_prefix_time_mem
end NDEAEvolve.Exp016
