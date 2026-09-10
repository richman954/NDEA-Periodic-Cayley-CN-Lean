import SpatialScalarRefinement

/-! The same full odd spatial grids with k=T/J for each fixed finite horizon.
This changes the comparison horizon explicitly, preserving the actual ordered
recurrence, samples, potential, and spatial reconstruction.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def horizonStepSize (T : ℝ) (q : ℕ) : ℝ := T * temporalStepSize q

theorem horizonStepSize_pos (T : ℝ) (hT : 0 < T) (q : ℕ) : 0 < horizonStepSize T q :=
  mul_pos hT (temporalStepSize_pos q)

theorem actualCayleyTime_constant (k : ℝ) (N : ℕ) :
    actualCayleyTime (fun _ => k) N = (N : ℝ) * k := by
  induction N with
  | zero => simp
  | succ N ih => rw [actualCayleyTime_succ, ih]; push_cast; ring

theorem horizonSchedule_time (T : ℝ) (q : ℕ) :
    actualCayleyTime (fun _ => horizonStepSize T q) (temporalStepCount q) = T := by
  rw [actualCayleyTime_constant, horizonStepSize, temporalStepSize]
  have hn : (temporalStepCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (temporalStepCount_pos q))
  field_simp [hn]

theorem horizonSchedule_prefix_time_mem (T : ℝ) (hT : 0 < T) (q N : ℕ)
    (hN : N ≤ temporalStepCount q) :
    actualCayleyTime (fun _ => horizonStepSize T q) N ∈ Set.Icc (0 : ℝ) T := by
  rw [actualCayleyTime_constant]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg N) (horizonStepSize_pos T hT q).le
  · calc
      _ ≤ (temporalStepCount q : ℝ) * horizonStepSize T q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (horizonStepSize_pos T hT q).le
      _ = T := by rw [← actualCayleyTime_constant, horizonSchedule_time]

theorem horizonSchedule_sum_cube (T : ℝ) (q : ℕ) :
    (∑ _j ∈ Finset.range (temporalStepCount q), (horizonStepSize T q)^3) =
      T^3 * (temporalStepSize q)^2 := by
  simp_rw [horizonStepSize, mul_pow]
  rw [← Finset.mul_sum, temporalSchedule_sum_cube]

theorem eventually_horizonStepSize_mul_le_one (T K : ℝ) :
    ∀ᶠ q : ℕ in atTop, |horizonStepSize T q| * K ≤ 1 := by
  filter_upwards [eventually_temporalStepSize_mul_le_one (|T| * K)] with q hq
  calc
    _ = |temporalStepSize q| * (|T| * K) := by rw [horizonStepSize, abs_mul]; ring
    _ ≤ 1 := hq

/-- Actual endpoint weights for every prefix, with T fixed before refinement. -/
theorem horizonCayley_doubleCutoff_fourierWeightedNorm_eventually_le (p S R : ℕ)
    (T : ℝ) (hT : 0 < T) (v : ℤ → E 2 →L[ℂ] E 2)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2)) :
    ∀ᶠ q : ℕ in atTop, ∀ j ≤ temporalStepCount q,
      fourierWeightedNorm p (initialSamplingCutoff q) (initialSamplingMesh q)
        (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q)
          (potentialCutoff R v)
          (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) (initialStateCutoff S a))
          (fun _ => horizonStepSize T q) j) ≤
      Real.exp (2 * (cutoffPotentialWeight p R v + 1) * T) * cutoffInitialWeight p S a := by
  filter_upwards [eventually_horizonStepSize_mul_le_one T (cutoffPotentialWeight p R v + 1)]
    with q hq
  intro j hj
  have hsum : (∑ _i ∈ Finset.range j, |horizonStepSize T q|) ≤ T := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      abs_of_pos (horizonStepSize_pos T hT q)]
    rw [← actualCayleyTime_constant]
    exact (horizonSchedule_prefix_time_mem T hT q j hj).2
  apply (sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le_horizon p
    (initialSamplingCutoff q) R (initialSamplingMesh q) (temporalSchedule_mesh q) v hHerm
    (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) (initialStateCutoff S a))
    (fun _ => horizonStepSize T q) j (fun _ _ => hq) T hsum).trans
  exact mul_le_mul_of_nonneg_left
    (sampledInitialState_cutoff_fourierWeightedNorm_le p (initialSamplingCutoff q) S
      (initialSamplingMesh q) (temporalSchedule_mesh q) a) (Real.exp_pos _).le

theorem horizonStep_generatorCoefficient_tendsto_zero (T K : ℝ) :
    Tendsto (fun q => horizonStepSize T q * (4 / (initialSamplingMesh q)^2 + K))
      atTop (𝓝 0) := by
  simpa only [horizonStepSize, mul_assoc, mul_zero] using
    (scheduledStep_generatorCoefficient_tendsto_zero K).const_mul T

#print axioms horizonStepSize_pos
#print axioms actualCayleyTime_constant
#print axioms horizonSchedule_time
#print axioms horizonSchedule_prefix_time_mem
#print axioms horizonSchedule_sum_cube
#print axioms eventually_horizonStepSize_mul_le_one
#print axioms horizonCayley_doubleCutoff_fourierWeightedNorm_eventually_le
#print axioms horizonStep_generatorCoefficient_tendsto_zero
end NDEAEvolve.Exp016
