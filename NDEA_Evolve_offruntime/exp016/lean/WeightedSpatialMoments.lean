import InitialWeightedCutoff
import AliasTailCertificate

/-! The propagated fourth weighted DFT sum controls the actual existing
stencil moment, low/high coefficient sums and spatial defect budget. These
bounds retain the original physical L2 normalization and complete alias tail.
The final consumer concerns actual trajectory endpoints; quadratic slab means,
velocities and generator-velocities remain separate obligations.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem frequencyWeight_one_le (p : ℕ) (m : ℤ) : 1 ≤ frequencyWeight p m :=
  one_le_pow₀ (Exp014.weight_one_le m)

theorem frequency_fourth_le_frequencyWeight (m : ℤ) :
    (m : ℝ)^4 ≤ frequencyWeight 2 m := by
  have he := pow_le_pow_left₀ (sq_nonneg (m : ℝ)) (Exp014.frequency_sq_le_weight m) 2
  simpa only [← pow_mul, frequencyWeight] using he

/-- The fourth l2 coefficient moment in the accepted stencil certificate. -/
theorem gridFourthCoefficientMoment_le_fourierWeightedNorm (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) :
    gridFourthCoefficientMoment M h y ≤ fourierWeightedNorm 2 M h y := by
  let f := fun m : Fin (2 * M + 1) =>
    (oddFrequency M m : ℝ)^4 * ‖fourierCoefficient M h y m‖
  have hf : ∀ m, 0 ≤ f m := by intro m; dsimp only [f]; positivity
  unfold gridFourthCoefficientMoment
  calc
    _ ≤ Real.sqrt ((∑ m, f m)^2) :=
      Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg (fun m _ => hf m))
    _ = ∑ m, f m := Real.sqrt_sq (Finset.sum_nonneg (fun m _ => hf m))
    _ ≤ fourierWeightedNorm 2 M h y := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_right (frequency_fourth_le_frequencyWeight _)
        (norm_nonneg _)

theorem gridLowCoefficientNorm_le_fourierWeightedNorm (p M R : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) :
    gridLowCoefficientNorm M h y R ≤ fourierWeightedNorm p M h y := by
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : |(oddFrequency M m : ℝ)| ≤ (R : ℝ)
  · simp only [if_pos hm]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (frequencyWeight_one_le p (oddFrequency M m))
        (norm_nonneg (fourierCoefficient M h y m))
  · simp only [if_neg hm]
    exact mul_nonneg (frequencyWeight_nonneg p _) (norm_nonneg _)

/-- The strict high-frequency coefficient tail has an explicit fourth-power bound. -/
theorem gridTailCoefficientNorm_le_fourthWeight (M R : ℕ) (h : ℝ)
    (y : Vec (Grid (2 * M))) :
    gridTailCoefficientNorm M h y R ≤ fourierWeightedNorm 2 M h y / (1 + (R : ℝ))^4 := by
  apply (le_div_iff₀ (show 0 < (1 + (R : ℝ))^4 by positivity)).mpr
  unfold gridTailCoefficientNorm fourierWeightedNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : |(oddFrequency M m : ℝ)| ≤ (R : ℝ)
  · rw [if_pos hm, zero_mul]
    exact mul_nonneg (frequencyWeight_nonneg 2 _) (norm_nonneg _)
  · rw [if_neg hm, mul_comm, frequencyWeight_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [lt_of_not_ge hm] : 1 + (R : ℝ) ≤ 1 + |(oddFrequency M m : ℝ)|) 4

/-- Both the retained low band and strict tail of the actual potential alias budget. -/
theorem potentialAliasTailBudget_le_fourthWeight (M R : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) :
    potentialAliasTailBudget M h v y R ≤
      (frequencyNormTail v (M - R) + (∑' ell, ‖v ell‖) / (1 + (R : ℝ))^4) *
        fourierWeightedNorm 2 M h y := by
  unfold potentialAliasTailBudget
  calc
    _ ≤ frequencyNormTail v (M - R) * fourierWeightedNorm 2 M h y +
        (∑' ell, ‖v ell‖) * (fourierWeightedNorm 2 M h y / (1 + (R : ℝ))^4) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (gridLowCoefficientNorm_le_fourierWeightedNorm 2 M R h y)
          (frequencyNormTail_nonneg v _))
        (mul_le_mul_of_nonneg_left (gridTailCoefficientNorm_le_fourthWeight M R h y)
          (tsum_nonneg (fun ell => norm_nonneg (v ell))))
    _ = _ := by ring

/-- Scalar coefficient multiplying the actual fourth weighted DFT sum. -/
def spatialFourthWeightCoefficient (M R : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) : ℝ :=
  Real.sqrt (2 * Real.pi) * h^2 + 2 * Real.sqrt (2 * Real.pi) *
    (frequencyNormTail v (M - R) + (∑' ell, ‖v ell‖) / (1 + (R : ℝ))^4)

theorem spatialFourthWeightCoefficient_nonneg (M R : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) :
    0 ≤ spatialFourthWeightCoefficient M R h v := by
  unfold spatialFourthWeightCoefficient
  exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg h))
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (add_nonneg (frequencyNormTail_nonneg v _)
        (div_nonneg (tsum_nonneg (fun ell => norm_nonneg (v ell))) (by positivity))))

/-- The existing complete stencil-plus-alias budget consumes the moment bounds. -/
theorem sampledSpatialTailBudget_le_fourthWeight (M R : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) :
    sampledSpatialTailBudget M h v y R ≤
      spatialFourthWeightCoefficient M R h v * fourierWeightedNorm 2 M h y := by
  unfold sampledSpatialTailBudget spatialFourthWeightCoefficient
  calc
    _ ≤ Real.sqrt (2 * Real.pi) * h^2 * fourierWeightedNorm 2 M h y +
        2 * Real.sqrt (2 * Real.pi) *
          ((frequencyNormTail v (M - R) + (∑' ell, ‖v ell‖) / (1 + (R : ℝ))^4) *
            fourierWeightedNorm 2 M h y) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (gridFourthCoefficientMoment_le_fourierWeightedNorm M h y)
          (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg h)))
        (mul_le_mul_of_nonneg_left (potentialAliasTailBudget_le_fourthWeight M R h v y)
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    _ = _ := by ring

/-- The actual physical L2 spatial-defect budget, for every grid state. -/
theorem sampledSpatialDefectBudget_le_fourthWeight (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (b : ℝ) :
    sampledSpatialDefectBudget M h v y b ≤
      spatialFourthWeightCoefficient M R h v * fourierWeightedNorm 2 M h y :=
  (sampledSpatialDefectBudget_le_tail M R hRM h hmesh v hv y b).trans
    (sampledSpatialTailBudget_le_fourthWeight M R h v y)

/-- Concrete consumer: the actual spatial budget at every trajectory endpoint.
The scalar spatial coefficient still needs a refinement limit, and the
quadratic slab's mean/velocity/generator terms are not omitted. -/
theorem scheduledCayley_doubleCutoff_spatialBudget_eventually_le (S R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (L : ℕ → ℕ)
    (hL : ∀ q, L q ≤ initialSamplingCutoff q) :
    ∀ᶠ q : ℕ in atTop, ∀ j ≤ temporalStepCount q,
      sampledSpatialDefectBudget (initialSamplingCutoff q) (initialSamplingMesh q)
        (potentialCutoff R v)
        (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q)
          (potentialCutoff R v)
          (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) (initialStateCutoff S a))
          (fun _ => temporalStepSize q) j) b ≤
      spatialFourthWeightCoefficient (initialSamplingCutoff q) (L q) (initialSamplingMesh q)
        (potentialCutoff R v) *
        (Real.exp (2 * (cutoffPotentialWeight 2 R v + 1)) * cutoffInitialWeight 2 S a) := by
  filter_upwards [scheduledCayley_doubleCutoff_fourierWeightedNorm_eventually_le 2 S R v hHerm a]
    with q hq
  intro j hj
  apply (sampledSpatialDefectBudget_le_fourthWeight (initialSamplingCutoff q) (L q)
    (hL q) (initialSamplingMesh q) (temporalSchedule_mesh q) (potentialCutoff R v)
    (potentialCutoff_regular R v) _ b).trans
  exact mul_le_mul_of_nonneg_left (hq j hj)
    (spatialFourthWeightCoefficient_nonneg _ _ _ _)

#print axioms frequencyWeight_one_le
#print axioms frequency_fourth_le_frequencyWeight
#print axioms gridFourthCoefficientMoment_le_fourierWeightedNorm
#print axioms gridLowCoefficientNorm_le_fourierWeightedNorm
#print axioms gridTailCoefficientNorm_le_fourthWeight
#print axioms potentialAliasTailBudget_le_fourthWeight
#print axioms spatialFourthWeightCoefficient_nonneg
#print axioms sampledSpatialTailBudget_le_fourthWeight
#print axioms sampledSpatialDefectBudget_le_fourthWeight
#print axioms scheduledCayley_doubleCutoff_spatialBudget_eventually_le
end NDEAEvolve.Exp016
