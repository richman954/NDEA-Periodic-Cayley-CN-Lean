import InitialSamplingBounds
import AliasTailCertificate

/-! The actual ordered Cayley certificate with a proved sampling initialization
budget. Arbitrary added initialization error is measured in the exact physical
grid norm; the Fourier tail is derived from the original continuum initial data.
-/
noncomputable section
open scoped BigOperators
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def sampledInitializationBudget (M : ℕ) (h : ℝ) (a : Exp014.FourierState (E 2))
    (y : Vec (Grid (2 * M))) : ℝ :=
  Real.sqrt h * ‖y - sampledInitialState M h a‖ +
    2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) M

theorem independentTarget_initialization_le_budget (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) (y : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y x - Exp014.synth a x)
      b (2 * Real.pi) ≤ sampledInitializationBudget M h a y := by
  rw [← fourierReconstruction_eq_independentTarget]
  exact initialization_spatialL2_le_tail M M le_rfl h hmesh a y b

/-- Exact nodal initialization leaves only the proved interpolation tail. -/
theorem sampledInitializationBudget_exact_samples (M : ℕ) (h : ℝ)
    (a : Exp014.FourierState (E 2)) :
    sampledInitializationBudget M h a (sampledInitialState M h a) =
      2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) M := by
  simp only [sampledInitializationBudget, sub_self, norm_zero, mul_zero, zero_add]

theorem sampledCayley_gridTime_initialized_error (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ)
    (hk : ∀ j < N, 0 < k j) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.rawFourier M h (sampledCayleyTrajectory M h v y₀ k N) x -
        Exp014.solution v a (actualCayleyTime k N) x) b (2 * Real.pi) ≤
      sampledInitializationBudget M h a y₀ +
      ∑ j ∈ Finset.range N, k j * sampledTailBudgetSequence M h v y₀ R k j := by
  refine (sampledCayley_gridTime_tail_error M R hRM h hmesh v hv hHerm a y₀ b k N hk).trans ?_
  exact add_le_add (independentTarget_initialization_le_budget M h hmesh a y₀ b) le_rfl

theorem sampledCayley_partialSlab_initialized_error (M R : ℕ) (hRM : R ≤ M) (h : ℝ)
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
      sampledInitializationBudget M h a y₀ +
      (∑ j ∈ Finset.range N, k j * sampledTailBudgetSequence M h v y₀ R k j) +
      (t - actualCayleyTime k N) * sampledTailBudgetSequence M h v y₀ R k N := by
  refine (sampledCayley_partialSlab_tail_error M R hRM h hmesh v hv hHerm a y₀ b k N t hk hkN ht).trans ?_
  exact add_le_add (add_le_add (independentTarget_initialization_le_budget M h hmesh a y₀ b)
    le_rfl) le_rfl

#print axioms independentTarget_initialization_le_budget
#print axioms sampledInitializationBudget_exact_samples
#print axioms sampledCayley_gridTime_initialized_error
#print axioms sampledCayley_partialSlab_initialized_error
end NDEAEvolve.Exp016
