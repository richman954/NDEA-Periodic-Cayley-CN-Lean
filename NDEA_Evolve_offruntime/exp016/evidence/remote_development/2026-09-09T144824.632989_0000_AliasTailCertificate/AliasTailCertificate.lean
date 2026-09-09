import PotentialAliasBounds
import QuantitativeCayleyCertificate

/-! The actual Cayley certificate consumes the proved potential-alias tails and
full-band stencil estimate. The remaining moments/tails belong to the actual
computed stages; their uniform refinement control is not assumed. -/
noncomputable section
open scoped BigOperators
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def gridFourthCoefficientMoment (M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) : ℝ :=
  Real.sqrt (∑ m : Fin (2 * M + 1),
    ((oddFrequency M m : ℝ)^4 * ‖fourierCoefficient M h y m‖)^2)

def sampledSpatialTailBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (R : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) * h^2 * gridFourthCoefficientMoment M h y +
    2 * Real.sqrt (2 * Real.pi) * potentialAliasTailBudget M h v y R

theorem sampledSpatialDefectBudget_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (b : ℝ) :
    sampledSpatialDefectBudget M h v y b ≤ sampledSpatialTailBudget M h v y R :=
  add_le_add (sampledStencilDefect_spatialL2_le M h hmesh y b)
    (sampledPotentialDefect_spatialL2_le_tailBudget M R hRM h hmesh v hv y b)

def sampledTailResidualBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (R : ℕ) (k : ℝ) : ℝ :=
  let A := sampledSplitA (2 * M) h
  let B := sampledSplitB (2 * M) h (operatorPotentialMatrix v)
  let G := op A + op B
  let y₃ := orderedCayleyEndpoint A B k y
  let m := quadraticMean y y₃
  let d := quadraticVelocity y y₃ k
  Real.sqrt h * (((k ^ 2 / 16) * ‖op A‖ * (‖op A‖ + 2 * ‖op B‖)^2 +
    (k ^ 2 / 8) * (‖op A‖ + ‖op B‖)^3) * ‖y‖) +
    sampledSpatialTailBudget M h v m R +
    (k / 2) * sampledSpatialTailBudget M h v d R +
    (k ^ 2 / 8) * sampledSpatialTailBudget M h v (G d) R

theorem sampledQuantitativeBudget_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 ≤ k) :
    sampledQuantitativeBudget M h v y b k ≤ sampledTailResidualBudget M h v y R k := by
  unfold sampledQuantitativeBudget sampledTailResidualBudget
  exact add_le_add
    (add_le_add (add_le_add le_rfl (sampledSpatialDefectBudget_le_tail M R hRM h hmesh v hv _ b))
      (mul_le_mul_of_nonneg_left (sampledSpatialDefectBudget_le_tail M R hRM h hmesh v hv _ b)
        (by positivity)))
    (mul_le_mul_of_nonneg_left (sampledSpatialDefectBudget_le_tail M R hRM h hmesh v hv _ b)
      (by positivity))

def sampledTailBudgetSequence (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (R : ℕ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  sampledTailResidualBudget M h v (sampledCayleyTrajectory M h v y₀ k j) R (k j)

theorem sampledQuantitativeBudgetSequence_le_tail (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (j : ℕ) (hk : 0 ≤ k j) :
    sampledQuantitativeBudgetSequence M h v y₀ b k j ≤
      sampledTailBudgetSequence M h v y₀ R k j :=
  sampledQuantitativeBudget_le_tail M R hRM h hmesh v hv _ b (k j) hk

theorem sampledCayley_gridTime_tail_error (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
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
      ∑ j ∈ Finset.range N, k j * sampledTailBudgetSequence M h v y₀ R k j := by
  refine (sampledCayley_gridTime_quantitative_error M h hmesh v hv hHerm a y₀ b k N hk).trans ?_
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  have hk' := hk j (Finset.mem_range.mp hj)
  exact mul_le_mul_of_nonneg_left
    (sampledQuantitativeBudgetSequence_le_tail M R hRM h hmesh v hv y₀ b k j hk'.le) hk'.le

theorem sampledCayley_partialSlab_tail_error (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
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
      (∑ j ∈ Finset.range N, k j * sampledTailBudgetSequence M h v y₀ R k j) +
      (t - actualCayleyTime k N) * sampledTailBudgetSequence M h v y₀ R k N := by
  refine (sampledCayley_partialSlab_quantitative_error M h hmesh v hv hHerm a y₀ b k N t hk hkN ht).trans ?_
  apply add_le_add
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j hj
    have hk' := hk j (Finset.mem_range.mp hj)
    exact mul_le_mul_of_nonneg_left
      (sampledQuantitativeBudgetSequence_le_tail M R hRM h hmesh v hv y₀ b k j hk'.le) hk'.le
  · exact mul_le_mul_of_nonneg_left
      (sampledQuantitativeBudgetSequence_le_tail M R hRM h hmesh v hv y₀ b k N hkN.le) (sub_nonneg.mpr ht.1)

#print axioms sampledSpatialDefectBudget_le_tail
#print axioms sampledQuantitativeBudget_le_tail
#print axioms sampledQuantitativeBudgetSequence_le_tail
#print axioms sampledCayley_gridTime_tail_error
#print axioms sampledCayley_partialSlab_tail_error
end NDEAEvolve.Exp016
