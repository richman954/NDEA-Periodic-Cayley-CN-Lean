import SpatialDefectCertificate
import OrderedStageBounds

/-! A finite-grid certificate with explicit temporal operator-norm constants.
The actual stencil and potential interpolation terms remain separate. These
constants are not asserted uniform under spatial refinement. -/
noncomputable section
open scoped BigOperators
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def sampledQuantitativeBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (b k : ℝ) : ℝ :=
  let A := sampledSplitA (2 * M) h
  let B := sampledSplitB (2 * M) h (operatorPotentialMatrix v)
  let G := op A + op B
  let y₃ := orderedCayleyEndpoint A B k y
  let m := quadraticMean y y₃
  let d := quadraticVelocity y y₃ k
  Real.sqrt h * (((k ^ 2 / 16) * ‖op A‖ * (‖op A‖ + 2 * ‖op B‖)^2 +
    (k ^ 2 / 8) * (‖op A‖ + ‖op B‖)^3) * ‖y‖) +
    sampledSpatialDefectBudget M h v m b +
    (k / 2) * sampledSpatialDefectBudget M h v d b +
    (k ^ 2 / 8) * sampledSpatialDefectBudget M h v (G d) b

theorem sampledSeparatedBudget_le_quantitative (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 < k) :
    sampledSeparatedBudget M h v y b k ≤ sampledQuantitativeBudget M h v y b k := by
  have hA := sampledSplitA_isHermitian (2 * M) h
  have hB := sampled_operatorPotential_splitB_isHermitian (2 * M) h v hHerm
  have hd := orderedCayleySplitDefect_norm_le _ _ k hA hB y
  have hv := orderedCayley_second_generator_velocity_norm_le _ _ k hk hA hB y
  unfold sampledSeparatedBudget sampledQuantitativeBudget
  apply add_le_add (add_le_add (add_le_add ?_ le_rfl) le_rfl) le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg h)
  exact (add_le_add hd (mul_le_mul_of_nonneg_left hv (by positivity))).trans_eq (by ring)

def sampledQuantitativeBudgetSequence (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  sampledQuantitativeBudget M h v (sampledCayleyTrajectory M h v y₀ k j) b (k j)

theorem sampledSeparatedBudgetSequence_le_quantitative (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (j : ℕ) (hk : 0 < k j) :
    sampledSeparatedBudgetSequence M h v y₀ b k j ≤
      sampledQuantitativeBudgetSequence M h v y₀ b k j :=
  sampledSeparatedBudget_le_quantitative M h v hHerm _ b (k j) hk

theorem sampledCayley_gridTime_quantitative_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ)
    (hk : ∀ j < N, 0 < k j) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.rawFourier M h (sampledCayleyTrajectory M h v y₀ k N) x -
        Exp014.solution v a (actualCayleyTime k N) x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      ∑ j ∈ Finset.range N, k j * sampledQuantitativeBudgetSequence M h v y₀ b k j := by
  refine (sampledCayley_gridTime_separated_error M h hmesh v hv hHerm a y₀ b k N hk).trans ?_
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  have hk' := hk j (Finset.mem_range.mp hj)
  exact mul_le_mul_of_nonneg_left
    (sampledSeparatedBudgetSequence_le_quantitative M h v hHerm y₀ b k j hk') hk'.le

theorem sampledCayley_partialSlab_quantitative_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hk : ∀ j < N, 0 < k j) (hkN : 0 < k N)
    (ht : t ∈ Icc (actualCayleyTime k N) (actualCayleyTime k N + k N)) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.actualCayleyFourierSlab M h (sampledSplitA (2 * M) h)
        (sampledSplitB (2 * M) h (operatorPotentialMatrix v))
        (sampledCayleyTrajectory M h v y₀ k N) (actualCayleyTime k N) (k N) t x -
        Exp014.solution v a t x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      (∑ j ∈ Finset.range N, k j * sampledQuantitativeBudgetSequence M h v y₀ b k j) +
      (t - actualCayleyTime k N) * sampledQuantitativeBudgetSequence M h v y₀ b k N := by
  refine (sampledCayley_partialSlab_separated_error M h hmesh v hv hHerm a y₀ b k N t hk hkN ht).trans ?_
  apply add_le_add
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j hj
    have hk' := hk j (Finset.mem_range.mp hj)
    exact mul_le_mul_of_nonneg_left
      (sampledSeparatedBudgetSequence_le_quantitative M h v hHerm y₀ b k j hk') hk'.le
  · exact mul_le_mul_of_nonneg_left
      (sampledSeparatedBudgetSequence_le_quantitative M h v hHerm y₀ b k N hkN) (sub_nonneg.mpr ht.1)

#print axioms sampledSeparatedBudget_le_quantitative
#print axioms sampledSeparatedBudgetSequence_le_quantitative
#print axioms sampledCayley_gridTime_quantitative_error
#print axioms sampledCayley_partialSlab_quantitative_error
end NDEAEvolve.Exp016
