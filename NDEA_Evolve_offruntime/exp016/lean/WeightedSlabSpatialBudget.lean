import WeightedSpatialMoments
import KineticSymbolBound

/-! The actual quadratic slab consumes the propagated weighted DFT bound.
The generator is the original centered kinetic operator plus sampled V_R;
the original split's Z terms cancel by the accepted exact decomposition.
All three spatial contributions and their k/2, k²/8 factors are retained.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem fourierWeightedNorm_gridKinetic_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (op (gridKinetic (2 * M) h) y) ≤
      (4 / h^2) * fourierWeightedNorm p M h y := by
  unfold fourierWeightedNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  calc
    _ ≤ frequencyWeight p (oddFrequency M m) *
        ((4 / h^2) * ‖fourierCoefficient M h y m‖) :=
      mul_le_mul_of_nonneg_left (fourierCoefficient_gridKinetic_norm_le M h hmesh y m hh)
        (frequencyWeight_nonneg p _)
    _ = _ := by ring

/-- The actual generator, with exact cancellation of the split offsets. -/
theorem fourierWeightedNorm_sampledGenerator_cutoff_le (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h
      ((op (sampledSplitA (2 * M) h) +
        op (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v)))) y) ≤
      (4 / h^2 + cutoffPotentialWeight p R v) * fourierWeightedNorm p M h y := by
  rw [sampled_generator_decomposition, _root_.add_apply]
  apply (fourierWeightedNorm_add_le p M h _ _).trans
  calc
    _ ≤ (4 / h^2) * fourierWeightedNorm p M h y +
        cutoffPotentialWeight p R v * fourierWeightedNorm p M h y :=
      add_le_add (fourierWeightedNorm_gridKinetic_le p M h hmesh hh y)
        (fourierWeightedNorm_sampledPotential_cutoff_le p M R h hmesh v y)
    _ = _ := by ring

theorem fourierWeightedNorm_quadraticMean_le (p M : ℕ) (h : ℝ)
    (y z : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (quadraticMean y z) ≤
      (fourierWeightedNorm p M h y + fourierWeightedNorm p M h z) / 2 := by
  rw [quadraticMean, fourierWeightedNorm_smul]
  have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hc]
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using
    mul_le_mul_of_nonneg_left (fourierWeightedNorm_add_le p M h y z)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem fourierWeightedNorm_quadraticVelocity_le (p M : ℕ) (h k : ℝ) (hk : 0 < k)
    (y z : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (quadraticVelocity y z k) ≤
      (fourierWeightedNorm p M h y + fourierWeightedNorm p M h z) / k := by
  rw [quadraticVelocity, fourierWeightedNorm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  simpa only [div_eq_mul_inv, mul_comm, add_comm] using
    mul_le_mul_of_nonneg_left (fourierWeightedNorm_sub_le p M h z y)
      (le_of_lt (inv_pos.mpr hk))

/-- Complete actual spatial slab budget; no residual term is assumed small. -/
theorem sampledSpatialStageBudget_cutoff_le_fourthWeight (M L R : ℕ) (hLM : L ≤ M)
    (h : ℝ) (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 < k) :
    sampledSpatialStageBudget M h (potentialCutoff R v) y b k ≤
      spatialFourthWeightCoefficient M L h (potentialCutoff R v) *
        (1 + k * (4 / h^2 + cutoffPotentialWeight 2 R v) / 8) *
        (fourierWeightedNorm 2 M h y + fourierWeightedNorm 2 M h
          (orderedCayleyEndpoint (sampledSplitA (2 * M) h)
            (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) k y)) := by
  let z := orderedCayleyEndpoint (sampledSplitA (2 * M) h)
    (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) k y
  let m := quadraticMean y z
  let d := quadraticVelocity y z k
  let G := op (sampledSplitA (2 * M) h) +
    op (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v)))
  let C := spatialFourthWeightCoefficient M L h (potentialCutoff R v)
  let K := 4 / h^2 + cutoffPotentialWeight 2 R v
  let Y := fourierWeightedNorm 2 M h y + fourierWeightedNorm 2 M h z
  have hC : 0 ≤ C := spatialFourthWeightCoefficient_nonneg _ _ _ _
  have hK : 0 ≤ K := add_nonneg (by positivity) (cutoffPotentialWeight_nonneg 2 R v)
  have hm : fourierWeightedNorm 2 M h m ≤ Y / 2 :=
    fourierWeightedNorm_quadraticMean_le 2 M h y z
  have hd : fourierWeightedNorm 2 M h d ≤ Y / k :=
    fourierWeightedNorm_quadraticVelocity_le 2 M h k hk y z
  have hGd : fourierWeightedNorm 2 M h (G d) ≤ K * (Y / k) :=
    (fourierWeightedNorm_sampledGenerator_cutoff_le 2 M R h hmesh hh v d).trans
      (mul_le_mul_of_nonneg_left hd hK)
  have hbudget (w : Vec (Grid (2 * M))) :
      sampledSpatialDefectBudget M h (potentialCutoff R v) w b ≤
        C * fourierWeightedNorm 2 M h w :=
    sampledSpatialDefectBudget_le_fourthWeight M L hLM h hmesh (potentialCutoff R v)
      (potentialCutoff_regular R v) w b
  change sampledSpatialDefectBudget M h (potentialCutoff R v) m b +
      (k / 2) * sampledSpatialDefectBudget M h (potentialCutoff R v) d b +
      (k^2 / 8) * sampledSpatialDefectBudget M h (potentialCutoff R v) (G d) b ≤
    C * (1 + k * K / 8) * Y
  calc
    _ ≤ C * (Y / 2) + (k / 2) * (C * (Y / k)) +
        (k^2 / 8) * (C * (K * (Y / k))) :=
      add_le_add
        (add_le_add ((hbudget m).trans (mul_le_mul_of_nonneg_left hm hC))
          (mul_le_mul_of_nonneg_left ((hbudget d).trans (mul_le_mul_of_nonneg_left hd hC))
            (by positivity)))
        (mul_le_mul_of_nonneg_left ((hbudget (G d)).trans
          (mul_le_mul_of_nonneg_left hGd hC)) (by positivity))
    _ = _ := by field_simp [ne_of_gt hk]; ring

/-- Concrete consumer: summing every actual slab to the actual time 1. -/
theorem scheduledSpatialSum_doubleCutoff_eventually_le (S R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (L : ℕ → ℕ)
    (hL : ∀ q, L q ≤ initialSamplingCutoff q) :
    ∀ᶠ q : ℕ in atTop,
      scheduledSpatialSum (potentialCutoff R v) (initialStateCutoff S a) b q ≤
        spatialFourthWeightCoefficient (initialSamplingCutoff q) (L q) (initialSamplingMesh q)
          (potentialCutoff R v) *
          (1 + temporalStepSize q *
            (4 / (initialSamplingMesh q)^2 + cutoffPotentialWeight 2 R v) / 8) *
          (2 * (Real.exp (2 * (cutoffPotentialWeight 2 R v + 1)) * cutoffInitialWeight 2 S a)) := by
  filter_upwards [scheduledCayley_doubleCutoff_fourierWeightedNorm_eventually_le 2 S R v hHerm a]
    with q hq
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := temporalStepSize q
  let y := sampledCayleyTrajectory M h (potentialCutoff R v)
    (sampledInitialState M h (initialStateCutoff S a)) (fun _ => k)
  let C := spatialFourthWeightCoefficient M (L q) h (potentialCutoff R v)
  let K := 4 / h^2 + cutoffPotentialWeight 2 R v
  let U := Real.exp (2 * (cutoffPotentialWeight 2 R v + 1)) * cutoffInitialWeight 2 S a
  have hk : 0 < k := temporalStepSize_pos q
  have hC : 0 ≤ C := spatialFourthWeightCoefficient_nonneg _ _ _ _
  have hK : 0 ≤ K := add_nonneg (by positivity) (cutoffPotentialWeight_nonneg 2 R v)
  have hfac : 0 ≤ C * (1 + k * K / 8) := by positivity
  change (∑ j ∈ Finset.range (temporalStepCount q),
      k * sampledSpatialStageBudget M h (potentialCutoff R v) (y j) b k) ≤
    C * (1 + k * K / 8) * (2 * U)
  calc
    _ ≤ ∑ _j ∈ Finset.range (temporalStepCount q),
        k * (C * (1 + k * K / 8) * (2 * U)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hk)
      have hb := sampledSpatialStageBudget_cutoff_le_fourthWeight M (L q) R (hL q)
        h (temporalSchedule_mesh q) (temporalSchedule_mesh_pos q) v (y j) b k hk
      have hy : orderedCayleyEndpoint (sampledSplitA (2 * M) h)
          (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) k (y j) =
          y (j + 1) := rfl
      rw [hy] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hfac
      have hj' : j < temporalStepCount q := Finset.mem_range.mp hj
      have h0 := hq j (by omega)
      have h1 := hq (j + 1) (by omega)
      change fourierWeightedNorm 2 M h (y j) ≤ U at h0
      change fourierWeightedNorm 2 M h (y (j + 1)) ≤ U at h1
      linarith
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc]
      have htime : (temporalStepCount q : ℝ) * k = 1 := by
        dsimp only [k, temporalStepSize]
        exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt (temporalStepCount_pos q)))
      rw [htime, one_mul]

#print axioms fourierWeightedNorm_gridKinetic_le
#print axioms fourierWeightedNorm_sampledGenerator_cutoff_le
#print axioms fourierWeightedNorm_quadraticMean_le
#print axioms fourierWeightedNorm_quadraticVelocity_le
#print axioms sampledSpatialStageBudget_cutoff_le_fourthWeight
#print axioms scheduledSpatialSum_doubleCutoff_eventually_le
end NDEAEvolve.Exp016
