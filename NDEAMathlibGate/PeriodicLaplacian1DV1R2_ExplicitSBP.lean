
import NDEAMathlibGate.PeriodicLaplacian1DV1R

noncomputable section

open Matrix Complex
open scoped BigOperators

namespace NDEAMathlibGate
namespace PeriodicLaplacian1DV1R2_ExplicitSBP

/-!
Append-only explicit finite-sum summation-by-parts layer.

This module imports and does not modify `PeriodicLaplacian1DV1R`.

The only new mathematical claim is the fully expanded weighted finite-sum
energy identity for the periodic one-dimensional negative Laplacian.

No consistency-order, temporal-consistency, PDE-convergence, PML,
infinite-dimensional, gauge-stability, or global-closure claim is made.
-/

/--
Pointwise cancellation of the positive real grid weight against one of the
two reciprocal-spacing factors in a squared forward difference.
-/
private theorem weighted_edge_term
    (h : ℝ)
    (hh : h ≠ 0)
    (z : ℂ) :
    (h : ℂ) *
        (star
            (PeriodicLaplacian1DV1R.invSpacing h * z) *
          (PeriodicLaplacian1DV1R.invSpacing h * z))
      =
    PeriodicLaplacian1DV1R.invSpacing h *
      (star z * z) := by
  have hmul :
      (h : ℂ) * PeriodicLaplacian1DV1R.invSpacing h = 1 := by
    have hhc : (h : ℂ) ≠ 0 := by
      exact_mod_cast hh
    simp [PeriodicLaplacian1DV1R.invSpacing, hhc]

  calc
    (h : ℂ) *
          (star
              (PeriodicLaplacian1DV1R.invSpacing h * z) *
            (PeriodicLaplacian1DV1R.invSpacing h * z))
        =
      ((h : ℂ) * PeriodicLaplacian1DV1R.invSpacing h) *
        PeriodicLaplacian1DV1R.invSpacing h *
          (star z * z) := by
            simp [
              star_mul,
              PeriodicLaplacian1DV1R.star_invSpacing
            ]
            ring
    _ =
      PeriodicLaplacian1DV1R.invSpacing h *
        (star z * z) := by
          rw [hmul]
          simp

/--
Intermediate edge-sum form. It remains private so that the public theorem
below exposes the fully expanded stencil and finite sums.
-/
private theorem weighted_summation_by_parts_edge_form
    {n : Nat}
    (h : ℝ)
    (hh : 0 < h)
    (v : Fin n → ℂ) :
    PeriodicLaplacian1DV1R.weightedInner h v
        ((PeriodicLaplacian1DV1R.periodicNegLaplacian h n).mulVec v)
      =
    PeriodicLaplacian1DV1R.invSpacing h *
      (∑ i : Fin n,
        star (PeriodicLaplacian1DV1R.edgeDifference v i) *
          PeriodicLaplacian1DV1R.edgeDifference v i) := by
  unfold PeriodicLaplacian1DV1R.weightedInner
  rw [PeriodicLaplacian1DV1R.gram_energy_identity]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    (h : ℂ) *
        (star
            ((PeriodicLaplacian1DV1R.forwardDiffMatrix h n).mulVec v i) *
          (PeriodicLaplacian1DV1R.forwardDiffMatrix h n).mulVec v i)
      =
    PeriodicLaplacian1DV1R.invSpacing h *
      (star (PeriodicLaplacian1DV1R.edgeDifference v i) *
        PeriodicLaplacian1DV1R.edgeDifference v i)
  simpa only [
    PeriodicLaplacian1DV1R.forwardDiffMatrix_mulVec_apply
  ] using
    weighted_edge_term
      h
      (ne_of_gt hh)
      (PeriodicLaplacian1DV1R.edgeDifference v i)

/--
Fully expanded weighted finite-sum summation-by-parts identity.

The left side is the weighted inner product with the periodic three-point
negative-Laplacian stencil. The right side is the reciprocal-grid-spacing
multiple of the finite sum of squared periodic forward edge differences.
-/
theorem weighted_finite_sum_summation_by_parts
    {n : Nat}
    (h : ℝ)
    (hh : 0 < h)
    (v : Fin n → ℂ) :
(h : ℂ) *
        (∑ i : Fin n,
          star (v i) *
            ((2 * v i
                - v (PeriodicShift1DV1.nextIdx i)
                - v (PeriodicShift1DV1.prevIdx i)) /
              (h : ℂ) ^ 2))
      =
    (h : ℂ)⁻¹ *
        (∑ i : Fin n,
          star
              (v (PeriodicShift1DV1.nextIdx i) - v i) *
            (v (PeriodicShift1DV1.nextIdx i) - v i))
:= by
  calc
    (h : ℂ) *
          (∑ i : Fin n,
            star (v i) *
              ((2 * v i
                  - v (PeriodicShift1DV1.nextIdx i)
                  - v (PeriodicShift1DV1.prevIdx i)) /
                (h : ℂ) ^ 2))
        =
      PeriodicLaplacian1DV1R.weightedInner h v
        ((PeriodicLaplacian1DV1R.periodicNegLaplacian h n).mulVec v) := by
          unfold PeriodicLaplacian1DV1R.weightedInner
          simp only [dotProduct]
          apply congrArg (fun z : ℂ => (h : ℂ) * z)
          apply Finset.sum_congr rfl
          intro i _hi
          apply congrArg (fun z : ℂ => star (v i) * z)
          exact
            (PeriodicLaplacian1DV1R.periodicNegLaplacian_mulVec_apply_total
              (n := n) h v i).symm
    _ =
      PeriodicLaplacian1DV1R.invSpacing h *
        (∑ i : Fin n,
          star (PeriodicLaplacian1DV1R.edgeDifference v i) *
            PeriodicLaplacian1DV1R.edgeDifference v i) :=
      weighted_summation_by_parts_edge_form
        (n := n) h hh v
    _ =
      (h : ℂ)⁻¹ *
        (∑ i : Fin n,
          star
              (v (PeriodicShift1DV1.nextIdx i) - v i) *
            (v (PeriodicShift1DV1.nextIdx i) - v i)) := by
      simpa only [
        PeriodicLaplacian1DV1R.invSpacing,
        PeriodicLaplacian1DV1R.edgeDifference
      ]


#check weighted_finite_sum_summation_by_parts

end PeriodicLaplacian1DV1R2_ExplicitSBP
end NDEAMathlibGate
