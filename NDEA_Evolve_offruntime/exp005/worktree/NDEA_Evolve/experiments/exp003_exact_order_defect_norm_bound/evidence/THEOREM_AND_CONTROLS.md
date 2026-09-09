# Verified theorem and controls

The modular log emits the public theorem with the requested universal scope:

```text
@NDEAEvolve.Exp003.cayley_order_defect_opNorm_le :
  ∀ {n : ℕ} (α β : ℝ) (A B : Mat n),
    Matrix.IsHermitian A → Matrix.IsHermitian B →
      ‖Chat A α * Chat B β - Chat B β * Chat A α‖ ≤
        4 * |α * β| *
          ‖operatorOf A * operatorOf B - operatorOf B * operatorOf A‖
```

`Chat`, `Rhat`, and `operatorOf` all have codomain
`E n →L[ℂ] E n`, with `E n = EuclideanSpace ℂ (Fin n)`. Every norm in the
statement and proof is therefore the induced continuous-linear-map operator
norm.

The proof transports Exp002's exact Cayley order-defect identity through
`Matrix.toEuclideanCLM`, applies `norm_smul`, proves the scalar norm is
`4 * |α * β|`, recursively applies `norm_mul_le`, and bounds the four resolvent
factors by Step 1's operator-norm contraction theorem.

The two compiled positive counterexample witnesses are:

- Missing absolute value: Pauli `X,Z`, `α = -1`, `β = 1`. Their transported
  commutator has positive norm, so the proposed right side without the absolute
  value is strictly negative while the left side is nonnegative.
- Missing factor four: Pauli `X,Z`, `α = β = 1/2`. The exact Cayley commutator
  is `(-16/25) • Khat`, hence its norm is `(16/25)‖Khat‖`, which is strictly
  greater than `(1/4)‖Khat‖` because `‖Khat‖ > 0`.

Both packaged control theorems include compiled proofs that Pauli `X` and `Z`
are Hermitian. Their norms are also norms on `E 2 →L[ℂ] E 2`.
