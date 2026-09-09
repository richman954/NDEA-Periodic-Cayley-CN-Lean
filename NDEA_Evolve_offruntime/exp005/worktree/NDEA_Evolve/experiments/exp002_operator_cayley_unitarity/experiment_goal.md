# NDEA-Evolve Experiment 002 — Audited Noncommutative Cayley Composition

Status: PREFLIGHT

## Mission

Build an audited Julia → Lean discovery-and-verification pipeline for finite-dimensional
complex Cayley transforms. The experiment lifts Experiment 001 from a scalar Fourier
eigenvalue to coupled Hermitian matrices and makes noncommutative order sensitivity
explicit.

For a complex square matrix `A` and real parameter `α`, define

`Dα(A) = I + i α A`, `Nα(A) = I - i α A`, and
`Cα(A) = Nα(A) Dα(A)⁻¹`.

The intended formal targets are:

1. If `A` is Hermitian, derive that `Dα(A)` is nonsingular.
2. Prove `Cα(A)` is unitary and preserves complex inner products and norms.
3. Prove any finite ordered product of such factors is unitary without assuming
   that distinct generators commute.
4. With `[X,Y] = XY - YX`, prove the exact order-defect identity

   `[Cα(A), Cβ(B)] = -4 α β Dα(A)⁻¹ Dβ(B)⁻¹ [A,B] Dβ(B)⁻¹ Dα(A)⁻¹`.

5. Under `αβ ≠ 0`, derive that the Cayley factors commute if and only if their
   generators commute.

Julia will construct exact Gaussian-rational examples and a structured certificate.
Lean will prove the general mathematical statements independently and will not trust
Julia's verdict.

## Significance

These ingredients are classical mathematics. The experiment's contribution is a
reusable, machine-audited noncommutative theorem layer and discovery pipeline for
later work on geometric integrators, coupled PDE discretizations, graph Laplacians,
and finite-dimensional quantum dynamics. It is not represented as a newly solved
open problem.

## Immutable predecessor

Experiment 001 is reference-only. No Experiment 001 file may be modified, rebuilt,
or repackaged. Its Chromebook evidence archive is the immutability sentinel with
SHA-256 `131a89fc12a0f7ae71011c50af7e359fd9c3f8ebbb974c982f77f9309c4127aa`.
