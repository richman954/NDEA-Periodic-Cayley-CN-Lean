import TargetBinding
import SynthesizedSlabError

/-! A finite-time certificate for the actual ordered Hermitian Cayley trajectory.
Every residual budget comes from its computed stages and spatial discrepancy.
The independent physical target and unrestricted initial mismatch are explicit.
No recurrence, residual-smallness, or spatial-refinement premise is assumed. -/
noncomputable section
open scoped BigOperators
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

section Recurrence
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualCayleyTrajectory (A B : Matrix ι ι ℂ) (y₀ : Vec ι) (k : ℕ → ℝ) : ℕ → Vec ι :=
  Nat.rec y₀ (fun j y => orderedCayleyEndpoint A B (k j) y)

@[simp] theorem actualCayleyTrajectory_zero (A B : Matrix ι ι ℂ)
    (y₀ : Vec ι) (k : ℕ → ℝ) : actualCayleyTrajectory A B y₀ k 0 = y₀ := rfl

@[simp] theorem actualCayleyTrajectory_succ (A B : Matrix ι ι ℂ)
    (y₀ : Vec ι) (k : ℕ → ℝ) (j : ℕ) :
    actualCayleyTrajectory A B y₀ k (j + 1) =
      orderedCayleyEndpoint A B (k j) (actualCayleyTrajectory A B y₀ k j) := rfl

end Recurrence

def actualCayleyTime (k : ℕ → ℝ) : ℕ → ℝ := Nat.rec 0 (fun j t => t + k j)

@[simp] theorem actualCayleyTime_zero (k : ℕ → ℝ) : actualCayleyTime k 0 = 0 := rfl

@[simp] theorem actualCayleyTime_succ (k : ℕ → ℝ) (j : ℕ) :
    actualCayleyTime k (j + 1) = actualCayleyTime k j + k j := rfl

def actualCayleyBudgetSequence (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (V : ℝ → E 2 →L[ℂ] E 2) (y₀ : Vec (Grid (2 * M)))
    (b : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  actualFourierResidualBudget M h A B V (actualCayleyTrajectory A B y₀ k j) b (k j)

/-- The actual recursively computed trajectory has a finite grid-time error
bound against Exp014's constructed solution, including its initial mismatch. -/
theorem actualCayley_gridTime_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ)
    (hk : ∀ j < N, 0 < k j) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.rawFourier M h (actualCayleyTrajectory A B y₀ k N) x -
        Exp014.solution v a (actualCayleyTime k N) x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      ∑ j ∈ Finset.range N,
        k j * actualCayleyBudgetSequence M h A B (Exp014.operatorPotential v) y₀ b k j := by
  have hbudget : ∀ j < N, ∀ t ∈ Icc (actualCayleyTime k j) (actualCayleyTime k j + k j),
      Exp015.spatialL2 (Exp015.pdeResidual (fun _ => Exp014.operatorPotential v)
        ((fourierRegularSynthesis M h).field
          (quadraticSlab (op A + op B) (actualCayleyTrajectory A B y₀ k j)
            (actualCayleyTrajectory A B y₀ k (j + 1)) (actualCayleyTime k j) (k j))) t)
        b (2 * Real.pi) ≤
      actualCayleyBudgetSequence M h A B (Exp014.operatorPotential v) y₀ b k j := by
    intro j hj t ht
    have he : (fourierRegularSynthesis M h).field
        (quadraticSlab (op A + op B) (actualCayleyTrajectory A B y₀ k j)
          (actualCayleyTrajectory A B y₀ k (j + 1)) (actualCayleyTime k j) (k j)) =
        actualFourierQuadratic M h A B (actualCayleyTrajectory A B y₀ k j)
          (actualCayleyTime k j) (k j) := by
      rw [fourierRegularSynthesis_field]
      rfl
    rw [he]
    exact actualFourierQuadratic_residual_spatialL2_le M h hmesh A B
      (Exp014.operatorPotential v) (Exp014.operatorPotential_continuous v hv)
      (actualCayleyTrajectory A B y₀ k j) b (actualCayleyTime k j) (k j) t
      (hk j hj).ne' hA hB ht
  have hc := (fourierRegularSynthesis M h).variable_potential_quadratic_slabs_error
    (op A + op B) (actualCayleyTrajectory A B y₀ k) (actualCayleyTime k) k
    (actualCayleyBudgetSequence M h A B (Exp014.operatorPotential v) y₀ b k) N
    v hv hHerm a b (actualCayleyTime_zero k) hk
    (fun j _ => actualCayleyTime_succ k j) hbudget
  simpa only [fourierRegularSynthesis_eval, actualCayleyTrajectory_zero,
    fourierReconstruction_eq_independentTarget] using hc

/-- A final partial slab adds only its elapsed duration times the derived
budget. The field is the independently specified actual Cayley/Fourier target. -/
theorem actualCayley_partialSlab_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hk : ∀ j < N, 0 < k j) (hkN : 0 < k N)
    (ht : t ∈ Icc (actualCayleyTime k N) (actualCayleyTime k N + k N)) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.actualCayleyFourierSlab M h A B
        (actualCayleyTrajectory A B y₀ k N) (actualCayleyTime k N) (k N) t x -
        Exp014.solution v a t x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      (∑ j ∈ Finset.range N,
        k j * actualCayleyBudgetSequence M h A B (Exp014.operatorPotential v) y₀ b k j) +
      (t - actualCayleyTime k N) *
        actualCayleyBudgetSequence M h A B (Exp014.operatorPotential v) y₀ b k N := by
  have hgrid := actualCayley_gridTime_error M h hmesh A B hA hB v hv hHerm a y₀ b k N hk
  have hslab := independentTarget_variable_potential_slab_error M h hmesh A B hA hB
    v hv hHerm a (actualCayleyTrajectory A B y₀ k N) b (actualCayleyTime k N)
    (k N) t hkN ht
  exact le_trans hslab (add_le_add hgrid le_rfl)

#print axioms actualCayleyTrajectory_zero
#print axioms actualCayleyTrajectory_succ
#print axioms actualCayleyTime_zero
#print axioms actualCayleyTime_succ
#print axioms actualCayley_gridTime_error
#print axioms actualCayley_partialSlab_error
end NDEAEvolve.Exp016
