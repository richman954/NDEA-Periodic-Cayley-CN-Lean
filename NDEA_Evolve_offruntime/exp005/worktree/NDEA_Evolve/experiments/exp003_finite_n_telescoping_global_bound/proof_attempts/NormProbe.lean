import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators

abbrev ProbeE (n : ℕ) := EuclideanSpace ℂ (Fin n)

theorem probe_pow_sub_pow_telescoping {R₀ : Type*} [Ring R₀]
    (S U : R₀) (N : ℕ) :
    S ^ N - U ^ N =
      ∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k := by
  let f : ℕ → R₀ := fun k => S ^ (N - k) * U ^ k
  calc
    S ^ N - U ^ N = f 0 - f N := by simp [f]
    _ = ∑ k ∈ Finset.range N, (f k - f (k + 1)) :=
      (Finset.sum_range_sub' f N).symm
    _ = ∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < N := Finset.mem_range.mp hk
      have hleft : N - k = (N - 1 - k) + 1 := by omega
      have hright : N - (k + 1) = N - 1 - k := by omega
      dsimp [f]
      rw [hleft, hright, pow_succ S, pow_succ' U]
      noncomm_ring

private theorem probe_unitary_sandwich_norm {n : ℕ}
    {S U D : ProbeE n →L[ℂ] ProbeE n}
    (hS : S ∈ unitary (ProbeE n →L[ℂ] ProbeE n))
    (hU : U ∈ unitary (ProbeE n →L[ℂ] ProbeE n))
    (p q : ℕ) :
    ‖S ^ p * D * U ^ q‖ = ‖D‖ := by
  have hSp : S ^ p ∈ unitary (ProbeE n →L[ℂ] ProbeE n) :=
    (unitary (ProbeE n →L[ℂ] ProbeE n)).pow_mem hS p
  have hUq : U ^ q ∈ unitary (ProbeE n →L[ℂ] ProbeE n) :=
    (unitary (ProbeE n →L[ℂ] ProbeE n)).pow_mem hU q
  calc
    ‖S ^ p * D * U ^ q‖ = ‖S ^ p * D‖ :=
      CStarRing.norm_mul_mem_unitary (S ^ p * D) hUq
    _ = ‖D‖ := CStarRing.norm_mem_unitary_mul D hSp

theorem probe_unitary_pow_sub_pow_opNorm_le {n : ℕ}
    (S U : ProbeE n →L[ℂ] ProbeE n) (N : ℕ)
    (hS : S ∈ unitary (ProbeE n →L[ℂ] ProbeE n))
    (hU : U ∈ unitary (ProbeE n →L[ℂ] ProbeE n)) :
    ‖S ^ N - U ^ N‖ ≤ (N : ℝ) * ‖S - U‖ := by
  rw [probe_pow_sub_pow_telescoping S U N]
  calc
    ‖∑ k ∈ Finset.range N,
        S ^ (N - 1 - k) * (S - U) * U ^ k‖ ≤
        ∑ k ∈ Finset.range N,
          ‖S ^ (N - 1 - k) * (S - U) * U ^ k‖ :=
      norm_sum_le _ _
    _ = ∑ _k ∈ Finset.range N, ‖S - U‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact probe_unitary_sandwich_norm hS hU (N - 1 - k) k
    _ = (N : ℝ) * ‖S - U‖ := by simp

#check @probe_unitary_pow_sub_pow_opNorm_le
#print axioms probe_unitary_pow_sub_pow_opNorm_le
