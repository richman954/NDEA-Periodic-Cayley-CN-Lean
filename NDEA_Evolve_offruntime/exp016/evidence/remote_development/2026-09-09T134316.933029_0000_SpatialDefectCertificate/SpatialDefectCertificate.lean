import SpatialDefectSplit

/-! Actual sampled Cayley certificates with separate stencil and potential
interpolation contributions. Every contribution is defined from the computed
stages. No spatial smallness or refinement premise is introduced. -/
noncomputable section
open scoped BigOperators
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def sampledSeparatedBudget (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y : Vec (Grid (2 * M))) (b k : ℝ) : ℝ :=
  let A := sampledSplitA (2 * M) h
  let B := sampledSplitB (2 * M) h (operatorPotentialMatrix v)
  let G := op A + op B
  let y₃ := orderedCayleyEndpoint A B k y
  let m := quadraticMean y y₃
  let d := quadraticVelocity y y₃ k
  Real.sqrt h * (‖orderedCayleySplitDefect A B k y‖ + (k ^ 2 / 8) * ‖G (G d)‖) +
    sampledSpatialDefectBudget M h v m b +
    (k / 2) * sampledSpatialDefectBudget M h v d b +
    (k ^ 2 / 8) * sampledSpatialDefectBudget M h v (G d) b

theorem sampledResidualBudget_le_separated (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (b k : ℝ) (hk : 0 ≤ k) :
    actualFourierResidualBudget M h (sampledSplitA (2 * M) h)
      (sampledSplitB (2 * M) h (operatorPotentialMatrix v)) (Exp014.operatorPotential v) y b k ≤
      sampledSeparatedBudget M h v y b k := by
  unfold actualFourierResidualBudget sampledSeparatedBudget
  exact add_le_add
    (add_le_add (add_le_add le_rfl (sampled_spatialDefect_spatialL2_le M h v hv _ b))
      (mul_le_mul_of_nonneg_left (sampled_spatialDefect_spatialL2_le M h v hv _ b)
        (by positivity)))
    (mul_le_mul_of_nonneg_left (sampled_spatialDefect_spatialL2_le M h v hv _ b)
      (by positivity))

/-- Exact residual of the actual ordered reconstruction, with its two spatial
discrepancies distinguished before taking any norm. -/
theorem sampledQuadratic_residual_split (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y : Vec (Grid (2 * M))) (t₀ k t x : ℝ) (hk : k ≠ 0) :
    let A := sampledSplitA (2 * M) h
    let B := sampledSplitB (2 * M) h (operatorPotentialMatrix v)
    let G := op A + op B
    let y₃ := orderedCayleyEndpoint A B k y
    let d := quadraticVelocity y y₃ k
    let q := quadraticSlab G y y₃ t₀ k t
    Exp015.pdeResidual (fun _ => Exp014.operatorPotential v)
      (actualFourierQuadratic M h A B y t₀ k) t x =
      fourierReconstruction M h (orderedCayleySplitDefect A B k y) x +
        quadraticCorrection t₀ k t • fourierReconstruction M h (G (G d)) x +
        (sampledStencilDefect M h x q + sampledPotentialDefect M h v x q) := by
  dsimp only
  rw [actualFourierQuadratic_residual M h _ _ _ y t₀ k t x hk
    (sampledSplitA_isHermitian (2 * M) h)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h v hHerm),
    sampled_spatialDefect_split]
  simp only [_root_.add_apply]

def sampledSeparatedBudgetSequence (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  sampledSeparatedBudget M h v (sampledCayleyTrajectory M h v y₀ k j) b (k j)

theorem sampledBudgetSequence_le_separated (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (j : ℕ) (hk : 0 ≤ k j) :
    sampledCayleyBudgetSequence M h v y₀ b k j ≤
      sampledSeparatedBudgetSequence M h v y₀ b k j :=
  sampledResidualBudget_le_separated M h v hv _ b (k j) hk

theorem sampledCayley_gridTime_separated_error (M : ℕ) (h : ℝ)
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
      ∑ j ∈ Finset.range N, k j * sampledSeparatedBudgetSequence M h v y₀ b k j := by
  refine (sampledCayley_gridTime_error M h hmesh v hv hHerm a y₀ b k N hk).trans ?_
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  have hk' := (hk j (Finset.mem_range.mp hj)).le
  exact mul_le_mul_of_nonneg_left
    (sampledBudgetSequence_le_separated M h v hv y₀ b k j hk') hk'

theorem sampledCayley_partialSlab_separated_error (M : ℕ) (h : ℝ)
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
      (∑ j ∈ Finset.range N, k j * sampledSeparatedBudgetSequence M h v y₀ b k j) +
      (t - actualCayleyTime k N) * sampledSeparatedBudgetSequence M h v y₀ b k N := by
  refine (sampledCayley_partialSlab_error M h hmesh v hv hHerm a y₀ b k N t hk hkN ht).trans ?_
  apply add_le_add
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j hj
    have hk' := (hk j (Finset.mem_range.mp hj)).le
    exact mul_le_mul_of_nonneg_left
      (sampledBudgetSequence_le_separated M h v hv y₀ b k j hk') hk'
  · exact mul_le_mul_of_nonneg_left
      (sampledBudgetSequence_le_separated M h v hv y₀ b k N hkN.le) (sub_nonneg.mpr ht.1)

#print axioms sampledResidualBudget_le_separated
#print axioms sampledQuadratic_residual_split
#print axioms sampledBudgetSequence_le_separated
#print axioms sampledCayley_gridTime_separated_error
#print axioms sampledCayley_partialSlab_separated_error
end NDEAEvolve.Exp016
