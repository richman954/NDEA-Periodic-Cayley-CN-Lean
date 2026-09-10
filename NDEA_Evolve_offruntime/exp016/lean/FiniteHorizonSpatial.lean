import WeightedSlabSpatialBudget
import FiniteHorizonSchedule

/-! Complete actual spatial residual accumulation for each fixed finite horizon.
This is an adaptation of the accepted time-1 slab/sum argument, retaining its
same constants and adding the exact total duration T. -/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def horizonSpatialSum (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) : ℝ :=
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := fun _ : ℕ => horizonStepSize T q
  let y₀ := sampledInitialState M h a
  ∑ j ∈ Finset.range (temporalStepCount q), k j *
    sampledSpatialStageBudget M h v (sampledCayleyTrajectory M h v y₀ k j) b (k j)

theorem sampledSpatialStageBudget_nonneg (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 ≤ k) :
    0 ≤ sampledSpatialStageBudget M h v y b k := by
  have hb (z : Vec (Grid (2 * M))) : 0 ≤ sampledSpatialDefectBudget M h v z b :=
    add_nonneg (Exp015.spatialL2_nonneg _ _ _) (Exp015.spatialL2_nonneg _ _ _)
  dsimp only [sampledSpatialStageBudget]
  exact add_nonneg (add_nonneg (hb _) (mul_nonneg (by positivity) (hb _)))
    (mul_nonneg (by positivity) (hb _))

theorem horizonSpatialSum_nonneg (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (hT : 0 < T) (q : ℕ) :
    0 ≤ horizonSpatialSum v a b T q := by
  unfold horizonSpatialSum
  exact Finset.sum_nonneg fun j _ => mul_nonneg (horizonStepSize_pos T hT q).le
    (sampledSpatialStageBudget_nonneg _ _ v _ b _ (horizonStepSize_pos T hT q).le)

/-- Concrete consumer: every actual slab to the exact fixed horizon T. -/
theorem horizonSpatialSum_doubleCutoff_eventually_le (S R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (L : ℕ → ℕ)
    (hL : ∀ q, L q ≤ initialSamplingCutoff q) :
    ∀ᶠ q : ℕ in atTop,
      horizonSpatialSum (potentialCutoff R v) (initialStateCutoff S a) b T q ≤
        spatialFourthWeightCoefficient (initialSamplingCutoff q) (L q) (initialSamplingMesh q)
          (potentialCutoff R v) *
          (1 + horizonStepSize T q *
            (4 / (initialSamplingMesh q)^2 + cutoffPotentialWeight 2 R v) / 8) *
          (2 * (Real.exp (2 * (cutoffPotentialWeight 2 R v + 1) * T) * cutoffInitialWeight 2 S a)) * T := by
  filter_upwards [horizonCayley_doubleCutoff_fourierWeightedNorm_eventually_le 2 S R T hT v hHerm a]
    with q hq
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := horizonStepSize T q
  let y := sampledCayleyTrajectory M h (potentialCutoff R v)
    (sampledInitialState M h (initialStateCutoff S a)) (fun _ => k)
  let C := spatialFourthWeightCoefficient M (L q) h (potentialCutoff R v)
  let K := 4 / h^2 + cutoffPotentialWeight 2 R v
  let U := Real.exp (2 * (cutoffPotentialWeight 2 R v + 1) * T) * cutoffInitialWeight 2 S a
  have hk : 0 < k := horizonStepSize_pos T hT q
  have hC : 0 ≤ C := spatialFourthWeightCoefficient_nonneg _ _ _ _
  have hK : 0 ≤ K := add_nonneg (by positivity) (cutoffPotentialWeight_nonneg 2 R v)
  have hfac : 0 ≤ C * (1 + k * K / 8) := by positivity
  change (∑ j ∈ Finset.range (temporalStepCount q),
      k * sampledSpatialStageBudget M h (potentialCutoff R v) (y j) b k) ≤
    C * (1 + k * K / 8) * (2 * U) * T
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
      have htime : (temporalStepCount q : ℝ) * k = T := by
        rw [← actualCayleyTime_constant]
        exact horizonSchedule_time T q
      rw [htime]
      ring


theorem horizonSpatialSum_doubleCutoff_tendsto_zero (S R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (horizonSpatialSum (potentialCutoff R v) (initialStateCutoff S a) b T)
      atTop (𝓝 0) := by
  have hc := spatialFourthWeightCoefficient_tendsto_zero (potentialCutoff R v)
    (potentialCutoff_regular R v)
  have hg := horizonStep_generatorCoefficient_tendsto_zero T (cutoffPotentialWeight 2 R v)
  have hm := ((hc.mul ((hg.div_const 8).const_add 1)).mul_const
    (2 * (Real.exp (2 * (cutoffPotentialWeight 2 R v + 1) * T) * cutoffInitialWeight 2 S a)))
      .mul_const T
  simp only [zero_div, add_zero, zero_mul] at hm
  exact squeeze_zero'
    (Eventually.of_forall (horizonSpatialSum_nonneg (potentialCutoff R v) (initialStateCutoff S a) b T hT))
    (horizonSpatialSum_doubleCutoff_eventually_le S R T hT v hHerm a b spatialLowCutoff spatialLowCutoff_le)
    hm

#print axioms sampledSpatialStageBudget_nonneg
#print axioms horizonSpatialSum_nonneg
#print axioms horizonSpatialSum_doubleCutoff_eventually_le
#print axioms horizonSpatialSum_doubleCutoff_tendsto_zero
end NDEAEvolve.Exp016
