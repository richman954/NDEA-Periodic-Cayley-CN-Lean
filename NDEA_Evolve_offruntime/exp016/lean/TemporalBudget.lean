import KineticAssembly
import QuantitativeCayleyCertificate
import CayleyPerturbation

/-! Concrete temporal constants for the actual ordered sampled scheme.
The coefficient is exactly the existing pointwise certificate's 1/16 and 1/8
coefficient. The spatial stage terms remain their actual computed expressions.
No evolved regularity or spatial-defect smallness is assumed here. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def temporalOperatorCoefficient (a b : ℝ) : ℝ :=
  a * (a + 2 * b)^2 / 16 + (a + b)^3 / 8

theorem temporalOperatorCoefficient_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ temporalOperatorCoefficient a b := by
  unfold temporalOperatorCoefficient
  positivity

theorem temporalOperatorCoefficient_mono (a b A B : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ A) (hb : b ≤ B) :
    temporalOperatorCoefficient a b ≤ temporalOperatorCoefficient A B := by
  unfold temporalOperatorCoefficient
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul ha
      (pow_le_pow_left₀ (by positivity)
        (add_le_add ha (mul_le_mul_of_nonneg_left hb (by norm_num))) 2)
      (sq_nonneg _) (ha0.trans ha)
  · exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (add_nonneg ha0 hb0) (add_le_add ha hb) 3) (by norm_num)

def physicalTemporalCoefficient (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2) : ℝ :=
  temporalOperatorCoefficient (4 / h^2 + 1) ((∑' ell : ℤ, ‖v ell‖) + 1)

theorem physicalTemporalCoefficient_nonneg (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2) :
    0 ≤ physicalTemporalCoefficient h v := by
  apply temporalOperatorCoefficient_nonneg
  · positivity
  · exact add_nonneg (tsum_nonneg fun _ => norm_nonneg _) (by norm_num)

theorem sampled_temporalOperatorCoefficient_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) :
    temporalOperatorCoefficient (‖op (sampledSplitA (2 * M) h)‖)
      (‖op (sampledSplitB (2 * M) h (operatorPotentialMatrix v))‖) ≤
      physicalTemporalCoefficient h v :=
  temporalOperatorCoefficient_mono _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (sampledSplitA_opNorm_le M h hmesh hh)
    (sampled_operatorPotential_splitB_opNorm_le (2 * M) h v hv)

def sampledTemporalBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (k : ℝ) : ℝ :=
  k^2 * temporalOperatorCoefficient (‖op (sampledSplitA (2 * M) h)‖)
    (‖op (sampledSplitB (2 * M) h (operatorPotentialMatrix v))‖) *
      (Real.sqrt h * ‖y‖)

def sampledSpatialStageBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (b k : ℝ) : ℝ :=
  let A := sampledSplitA (2 * M) h
  let B := sampledSplitB (2 * M) h (operatorPotentialMatrix v)
  let G := op A + op B
  let y₃ := orderedCayleyEndpoint A B k y
  let m := quadraticMean y y₃
  let d := quadraticVelocity y y₃ k
  sampledSpatialDefectBudget M h v m b +
    (k / 2) * sampledSpatialDefectBudget M h v d b +
    (k^2 / 8) * sampledSpatialDefectBudget M h v (G d) b

/-- Exact extraction from the existing quantitative certificate, without
changing its spatial mean, velocity or generator-velocity contributions. -/
theorem sampledQuantitativeBudget_eq_temporal_add_spatial (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) (b k : ℝ) :
    sampledQuantitativeBudget M h v y b k =
      sampledTemporalBudget M h v y k + sampledSpatialStageBudget M h v y b k := by
  unfold sampledQuantitativeBudget sampledTemporalBudget sampledSpatialStageBudget
    temporalOperatorCoefficient
  ring

def sampledTemporalSum (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, k j *
    sampledTemporalBudget M h v (sampledCayleyTrajectory M h v y₀ k j) (k j)

theorem sampledTemporalSum_eq (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y₀ : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ) :
    sampledTemporalSum M h v y₀ k N = (Real.sqrt h * ‖y₀‖) *
      temporalOperatorCoefficient (‖op (sampledSplitA (2 * M) h)‖)
        (‖op (sampledSplitB (2 * M) h (operatorPotentialMatrix v))‖) *
      ∑ j ∈ Finset.range N, (k j)^3 := by
  unfold sampledTemporalSum sampledTemporalBudget sampledCayleyTrajectory
  simp only [actualCayleyTrajectory_norm _ _ (sampledSplitA_isHermitian (2 * M) h)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h v hHerm)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sampledTemporalSum_nonneg (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y₀ : Vec (Grid (2 * M)))
    (k : ℕ → ℝ) (N : ℕ) (hk : ∀ j < N, 0 ≤ k j) :
    0 ≤ sampledTemporalSum M h v y₀ k N := by
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (hk j (Finset.mem_range.mp hj))
  unfold sampledTemporalBudget
  exact mul_nonneg (mul_nonneg (sq_nonneg _)
    (temporalOperatorCoefficient_nonneg _ _ (norm_nonneg _) (norm_nonneg _)))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- A concrete mesh/potential bound for arbitrary nonnegative variable steps.
Unitarity removes dependence on the intermediate numerical states. -/
theorem sampledTemporalSum_le_physical (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (y₀ : Vec (Grid (2 * M)))
    (k : ℕ → ℝ) (N : ℕ) (hk : ∀ j < N, 0 ≤ k j) :
    sampledTemporalSum M h v y₀ k N ≤
      (Real.sqrt h * ‖y₀‖) * physicalTemporalCoefficient h v *
        ∑ j ∈ Finset.range N, (k j)^3 := by
  rw [sampledTemporalSum_eq M h v hHerm]
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sampled_temporalOperatorCoefficient_le M h hmesh hh v hv)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
  exact Finset.sum_nonneg fun j hj => pow_nonneg (hk j (Finset.mem_range.mp hj)) 3

/-- The actual PDE error certificate with explicit temporal constants and
unchanged computed spatial defects. Initial mismatch remains unrestricted. -/
theorem sampledCayley_gridTime_explicitTemporal_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (hh : 0 < h)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ)
    (hk : ∀ j < N, 0 < k j) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.rawFourier M h (sampledCayleyTrajectory M h v y₀ k N) x -
        Exp014.solution v a (actualCayleyTime k N) x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      (Real.sqrt h * ‖y₀‖) * physicalTemporalCoefficient h v *
        (∑ j ∈ Finset.range N, (k j)^3) +
      ∑ j ∈ Finset.range N, k j * sampledSpatialStageBudget M h v
        (sampledCayleyTrajectory M h v y₀ k j) b (k j) := by
  have he := sampledCayley_gridTime_quantitative_error M h hmesh v hv hHerm a y₀ b k N hk
  simp only [sampledQuantitativeBudgetSequence,
    sampledQuantitativeBudget_eq_temporal_add_spatial, mul_add, Finset.sum_add_distrib] at he
  rw [← sampledTemporalSum, ← add_assoc] at he
  exact he.trans (add_le_add (add_le_add le_rfl
    (sampledTemporalSum_le_physical M h hmesh hh v hv hHerm y₀ k N
      (fun j hj => (hk j hj).le))) le_rfl)

#print axioms temporalOperatorCoefficient_nonneg
#print axioms temporalOperatorCoefficient_mono
#print axioms physicalTemporalCoefficient_nonneg
#print axioms sampled_temporalOperatorCoefficient_le
#print axioms sampledQuantitativeBudget_eq_temporal_add_spatial
#print axioms sampledTemporalSum_eq
#print axioms sampledTemporalSum_nonneg
#print axioms sampledTemporalSum_le_physical
#print axioms sampledCayley_gridTime_explicitTemporal_error
end NDEAEvolve.Exp016
