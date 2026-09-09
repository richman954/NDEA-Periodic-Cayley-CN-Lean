# Verified theorems and controls

The modular log emits the public exact identity with universal scope:

```text
@NDEAEvolve.Exp003.cayley_split_unsplit_defect :
  ∀ {n : ℕ} (alpha : ℝ) (A B : Mat n),
    Matrix.IsHermitian A → Matrix.IsHermitian B →
      cayley alpha A * cayley alpha B - cayley alpha (A + B) =
        (2 * (alpha : ℂ)^2) •
          (cayleyR alpha (A + B) * B * A * cayleyR alpha A *
             cayleyR alpha B -
           A * cayleyR alpha A * B * cayleyR alpha B)
```

It also emits the induced operator-norm theorem:

```text
@NDEAEvolve.Exp003.cayley_split_unsplit_defect_opNorm_le :
  ∀ {n : ℕ} (alpha : ℝ) (A B : Mat n),
    Matrix.IsHermitian A → Matrix.IsHermitian B →
      ‖Chat A alpha * Chat B alpha - Chat (A + B) alpha‖ ≤
        4 * alpha^2 * ‖operatorOf A‖ * ‖operatorOf B‖
```

`Chat`, `Rhat`, and `operatorOf` have codomain
`E n →L[ℂ] E n`, with `E n = EuclideanSpace ℂ (Fin n)`. Every norm in the
statement and proof is therefore the induced continuous-linear-map operator
norm.

The arbitrary-ring theorem `cayley_split_defect_core` proves the algebraic
heart by noncommutative expansion and inverse laws. Substitution
`X = i alpha A`, `Y = i alpha B` and `(i alpha)^2 = -alpha^2` gives the stated
matrix ordering and sign. The CLM proof transports the identity through
`Matrix.toEuclideanCLM`, applies `norm_smul` and `norm_sub_le`, recursively
applies `norm_mul_le`, and uses the Step 1 contraction theorem for
`R_A`, `R_B`, and `R_(A+B)`.

The controls compile as follows:

- `commutative_collapse_counterexample`: at `A = B = I_1`, `alpha = 1`, both
  generators are Hermitian and commute, but the exact defect is
  `((-2 + 4i)/5) I_1`, hence is nonzero.
- `absolute_linear_bound_holds_of_abs_le_one`: for every Hermitian `A,B` and
  every `|alpha| <= 1`, the quadratic theorem entails the proposed bound with
  `4 * |alpha|`. This certifies that the requested small-step negative witness
  cannot exist.
- `missing_alpha_square_large_step_counterexample`: at `alpha = 10` and
  `A = B = (1/10) I_1`, the proposed globally quantified linear bound is
  false. Its right side is `2/5`, whereas the defect norm is `2/sqrt(5)`.
