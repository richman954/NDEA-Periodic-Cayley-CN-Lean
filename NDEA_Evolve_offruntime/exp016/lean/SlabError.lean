import VariablePotentialBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Slabwise error accumulation against one actual classical solution.

Each slab has its own globally regular extension. Only its two endpoint values
are identified with the numerical profiles. No global differentiability of the
assembled path is used. The initial mismatch remains in every estimate.
-/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp016

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite positive-time slabs accumulate their actual residual budgets with
coefficient one. Ordered times also allow a zero-length slab. -/
theorem slabwise_residual_error_uniform_budget
    (w : ℕ → ℝ → ℝ → H) (z : ℕ → ℝ → H) (u : ℝ → ℝ → H)
    (V : ℝ → ℝ → H →L[ℂ] H) (L b : ℝ)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x))
    (hVc : Continuous (fun p : ℝ × ℝ => V p.1 p.2)) (hL : 0 < L)
    (τ B : ℕ → ℝ) (N : ℕ)
    (hw : ∀ j < N, Exp015.IsRegularPeriodicField L (w j))
    (hstep : ∀ j < N, τ j ≤ τ (j + 1))
    (hleft : ∀ j < N, w j (τ j) = z j)
    (hright : ∀ j < N, w j (τ (j + 1)) = z (j + 1))
    (hbudget : ∀ j < N, ∀ t ∈ Set.Icc (τ j) (τ (j + 1)),
      Exp015.spatialL2 (Exp015.pdeResidual V (w j) t) b L ≤ B j) :
    Exp015.spatialL2 (fun x => z N x - u (τ N) x) b L ≤
      Exp015.spatialL2 (fun x => z 0 x - u (τ 0) x) b L +
        ∑ j ∈ Finset.range N, (τ (j + 1) - τ j) * B j := by
  let E : ℕ → ℝ := fun j => Exp015.spatialL2 (fun x => z j x - u (τ j) x) b L
  have hlocal (j : ℕ) (hj : j < N) : E (j + 1) - E j ≤
      (τ (j + 1) - τ j) * B j := by
    have h := Exp015.residual_error_uniform_budget (w j) u (hw j hj) hu hV hL
      (Exp015.pdeResidual_continuous V (w j) (hw j hj) hVc)
      b (τ j) (τ (j + 1)) (B j) (hstep j hj) (hbudget j hj)
    rw [hleft j hj, hright j hj] at h
    change E (j + 1) ≤ E j + (τ (j + 1) - τ j) * B j at h
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using h)
  have hsum : (∑ j ∈ Finset.range N, (E (j + 1) - E j)) ≤
      ∑ j ∈ Finset.range N, (τ (j + 1) - τ j) * B j :=
    Finset.sum_le_sum fun j hj => hlocal j (Finset.mem_range.mp hj)
  rw [Finset.sum_range_sub] at hsum
  change E N ≤ E 0 + _
  exact (sub_le_iff_le_add.mp hsum).trans_eq (add_comm _ _)

/-- At a time inside the next slab, add only that slab's elapsed-time budget.
Agreement of derivatives at the grid times is not a premise. -/
theorem slabwise_residual_error_partial_slab
    (w : ℕ → ℝ → ℝ → H) (z : ℕ → ℝ → H) (u : ℝ → ℝ → H)
    (V : ℝ → ℝ → H →L[ℂ] H) (L b : ℝ)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x))
    (hVc : Continuous (fun p : ℝ × ℝ => V p.1 p.2)) (hL : 0 < L)
    (τ B : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hw : ∀ j ≤ N, Exp015.IsRegularPeriodicField L (w j))
    (hstep : ∀ j < N, τ j ≤ τ (j + 1))
    (hleft : ∀ j ≤ N, w j (τ j) = z j)
    (hright : ∀ j < N, w j (τ (j + 1)) = z (j + 1))
    (hbudget : ∀ j ≤ N, ∀ r ∈ Set.Icc (τ j) (τ (j + 1)),
      Exp015.spatialL2 (Exp015.pdeResidual V (w j) r) b L ≤ B j)
    (ht : t ∈ Set.Icc (τ N) (τ (N + 1))) :
    Exp015.spatialL2 (fun x => w N t x - u t x) b L ≤
      Exp015.spatialL2 (fun x => z 0 x - u (τ 0) x) b L +
        (∑ j ∈ Finset.range N, (τ (j + 1) - τ j) * B j) + (t - τ N) * B N := by
  have hnodes := slabwise_residual_error_uniform_budget w z u V L b hu hV hVc hL
    τ B N (fun j hj => hw j (Nat.le_of_lt hj)) hstep
    (fun j hj => hleft j (Nat.le_of_lt hj)) hright
    (fun j hj => hbudget j (Nat.le_of_lt hj))
  have hlast := Exp015.residual_error_uniform_budget (w N) u (hw N le_rfl) hu hV hL
    (Exp015.pdeResidual_continuous V (w N) (hw N le_rfl) hVc)
    b (τ N) t (B N) ht.1
    (fun r hr => hbudget N le_rfl r ⟨hr.1, hr.2.trans ht.2⟩)
  rw [hleft N le_rfl] at hlast
  exact hlast.trans (add_le_add hnodes (le_refl _))

/-- The accumulated certificate applies to Exp014's constructed variable-
potential solution. Arbitrary numerical initial profiles retain their full
mismatch with the Fourier datum. -/
theorem variable_potential_slabwise_error
    (v : ℤ → H →L[ℂ] H) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState H)
    (w : ℕ → ℝ → ℝ → H) (z : ℕ → ℝ → H) (b : ℝ)
    (τ B : ℕ → ℝ) (N : ℕ) (hzero : τ 0 = 0)
    (hw : ∀ j < N, Exp015.IsRegularPeriodicField (2 * Real.pi) (w j))
    (hstep : ∀ j < N, τ j ≤ τ (j + 1))
    (hleft : ∀ j < N, w j (τ j) = z j)
    (hright : ∀ j < N, w j (τ (j + 1)) = z (j + 1))
    (hbudget : ∀ j < N, ∀ t ∈ Set.Icc (τ j) (τ (j + 1)),
      Exp015.spatialL2
        (Exp015.pdeResidual (fun _ x => Exp014.operatorPotential v x) (w j) t)
        b (2 * Real.pi) ≤ B j) :
    Exp015.spatialL2 (fun x => z N x - Exp014.solution v a (τ N) x)
      b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => z 0 x - Exp014.synth a x) b (2 * Real.pi) +
        ∑ j ∈ Finset.range N, (τ (j + 1) - τ j) * B j := by
  have h := slabwise_residual_error_uniform_budget w z (Exp014.solution v a)
    (fun _ x => Exp014.operatorPotential v x) (2 * Real.pi) b
    (Exp014.solution_classical v hv a)
    (fun _ x => Exp014.operatorPotential_selfAdjoint v hHerm x)
    ((Exp014.operatorPotential_continuous v hv).comp continuous_snd)
    (by positivity) τ B N hw hstep hleft hright hbudget
  simpa only [hzero, Exp014.solution_zero] using h

#print axioms slabwise_residual_error_uniform_budget
#print axioms slabwise_residual_error_partial_slab
#print axioms variable_potential_slabwise_error

end NDEAEvolve.Exp016
