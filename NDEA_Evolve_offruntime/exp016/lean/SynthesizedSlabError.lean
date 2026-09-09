import SlabError
import RegularSynthesis

/-! Error accumulation for the actual quadratic slab field through regular
spatial synthesis. Nodal data need not match the reference initial datum. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp016

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RegularSynthesis

/-- Exact quadratic endpoint recovery discharges all nodal matching and slab
regularity premises of the finite residual accumulation theorem. -/
theorem quadratic_slabs_error {L : ℝ} (S : RegularSynthesis E H L)
    (G : E →L[ℂ] E) (y : ℕ → E) (τ k B : ℕ → ℝ) (N : ℕ)
    (u : ℝ → ℝ → H) (V : ℝ → H →L[ℂ] H) (b : ℝ)
    (hu : Exp013.IsClassicalPeriodicSolution L (fun _ => V) 0 u)
    (hV : ∀ x, IsSelfAdjoint (V x)) (hVc : Continuous V) (hL : 0 < L)
    (hk : ∀ j < N, 0 < k j)
    (hτ : ∀ j < N, τ (j + 1) = τ j + k j)
    (hbudget : ∀ j < N, ∀ t ∈ Set.Icc (τ j) (τ j + k j),
      Exp015.spatialL2
        (Exp015.pdeResidual (fun _ => V)
          (S.field (quadraticSlab G (y j) (y (j + 1)) (τ j) (k j))) t) b L ≤ B j) :
    Exp015.spatialL2 (fun x => S.eval x (y N) - u (τ N) x) b L ≤
      Exp015.spatialL2 (fun x => S.eval x (y 0) - u (τ 0) x) b L +
        ∑ j ∈ Finset.range N, k j * B j := by
  have h := slabwise_residual_error_uniform_budget
    (fun j => S.field (quadraticSlab G (y j) (y (j + 1)) (τ j) (k j)))
    (fun j x => S.eval x (y j)) u (fun _ => V) L b hu (fun _ => hV)
    (hVc.comp continuous_snd) hL τ B N
    (fun j _ => S.quadratic_field_regular G (quadraticMean (y j) (y (j + 1)))
      (quadraticVelocity (y j) (y (j + 1)) (k j)) (τ j) (k j))
    (by intro j hj; rw [hτ j hj]; linarith [hk j hj])
    (by intro j hj; funext x; exact S.quadratic_slab_left G _ _ _ _ x (hk j hj).ne')
    (by
      intro j hj
      rw [hτ j hj]
      funext x
      exact S.quadratic_slab_right G _ _ _ _ x (hk j hj).ne')
    (by intro j hj; simpa only [hτ j hj] using hbudget j hj)
  have hsum : (∑ j ∈ Finset.range N, (τ (j + 1) - τ j) * B j) =
      ∑ j ∈ Finset.range N, k j * B j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hτ j (Finset.mem_range.mp hj), add_sub_cancel_left]
  rw [hsum] at h
  exact h

/-- The concrete reference is Exp014's constructed solution, and the full
numerical initial mismatch remains visible after exact endpoint recovery. -/
theorem variable_potential_quadratic_slabs_error
    (S : RegularSynthesis E H (2 * Real.pi))
    (G : E →L[ℂ] E) (y : ℕ → E) (τ k B : ℕ → ℝ) (N : ℕ)
    (v : ℤ → H →L[ℂ] H) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState H) (b : ℝ)
    (hzero : τ 0 = 0) (hk : ∀ j < N, 0 < k j)
    (hτ : ∀ j < N, τ (j + 1) = τ j + k j)
    (hbudget : ∀ j < N, ∀ t ∈ Set.Icc (τ j) (τ j + k j),
      Exp015.spatialL2
        (Exp015.pdeResidual (fun _ x => Exp014.operatorPotential v x)
          (S.field (quadraticSlab G (y j) (y (j + 1)) (τ j) (k j))) t)
        b (2 * Real.pi) ≤ B j) :
    Exp015.spatialL2
        (fun x => S.eval x (y N) - Exp014.solution v a (τ N) x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => S.eval x (y 0) - Exp014.synth a x) b (2 * Real.pi) +
        ∑ j ∈ Finset.range N, k j * B j := by
  have h := S.quadratic_slabs_error G y τ k B N (Exp014.solution v a)
    (Exp014.operatorPotential v) b (Exp014.solution_classical v hv a)
    (Exp014.operatorPotential_selfAdjoint v hHerm)
    (Exp014.operatorPotential_continuous v hv) (by positivity) hk hτ hbudget
  simpa only [hzero, Exp014.solution_zero] using h

#print axioms quadratic_slabs_error
#print axioms variable_potential_quadratic_slabs_error

end RegularSynthesis
end NDEAEvolve.Exp016
