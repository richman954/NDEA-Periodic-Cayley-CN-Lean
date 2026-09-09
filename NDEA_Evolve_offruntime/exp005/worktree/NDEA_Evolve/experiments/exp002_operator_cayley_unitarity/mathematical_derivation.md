# Mathematical derivation and verification boundary

## Definitions and conventions

For a finite square complex matrix `A` and a real scalar `α`, let

```text
X       = i α A
Dα(A)   = I + X
Nα(A)   = I - X
Rα(A)   = Dα(A)⁻¹
Cα(A)   = Nα(A) Rα(A).
```

The commutator convention is `[P,Q] = PQ - QP`. Products act on column
vectors from right to left. Consequently, the chronological list
`[C₁,C₂,C₃]` is represented by `C₃ C₂ C₁`, so the head step acts first.

## Hermitian denominator and unitarity

If `A* = A` and `α` is real, then `X* = -X`. Hence

```text
D* D = (I-X)(I+X) = I - X² = I + X*X.
```

In finite dimension, `I + X*X` is positive definite, hence invertible. If
`Dv = 0`, injectivity of `D*D` gives `v = 0`; for a square finite matrix this
makes `D` invertible. This establishes denominator nonsingularity from
Hermiticity rather than assuming it.

Moreover `D` is normal and `N = D*`. With `R = D⁻¹`, normality makes `R`
commute with `D*`, and direct ordered cancellation proves

```text
C C* = I,
C* C = I.
```

Thus the associated continuous linear map preserves the standard complex
Euclidean inner product and norm.

For a chronological list of factors, induction uses only

```text
(UV)(UV)* = U(VV*)U* = I,
(UV)*(UV) = V*(U*U)V = I.
```

No exchange of `U` and `V` occurs. Therefore generators and steps may vary and
no pairwise commutation premise is needed.

## Exact noncommutative order defect

Let `D = I+X`, `E = I+Y`, with two-sided inverses `R` and `S`. First,

```text
(I-X)R = 2R-I,
(I-Y)S = 2S-I.
```

Direct ordered multiplication gives the inverse-commutator identity

```text
[R,S] = R S [D,E] S R = R S [X,Y] S R.
```

It follows that

```text
[(I-X)R,(I-Y)S] = 4 R S [X,Y] S R.
```

For `X=iαA`, `Y=iβB`, scalar centrality and `i²=-1` give

```text
[X,Y] = -αβ[A,B].
```

Combining these identities yields the frozen formula

```text
[Cα(A),Cβ(B)]
  = -4 α β Rα(A) Rβ(B) [A,B] Rβ(B) Rα(A).
```

Hermiticity is not needed for this algebraic theorem; the explicit assumptions
are the four two-sided inverse laws. For Hermitian generators and real steps,
the preceding finite-dimensional argument supplies those laws.

If `αβ ≠ 0`, the scalar coefficient is nonzero. Multiplication on the left by
`DβDα` and on the right by `DαDβ` cancels the ordered inverse sandwich, so the
Cayley commutator vanishes exactly when `[A,B]` vanishes.

## Important ordering nuance

Reversing both inverse pairs produces

```text
Rβ Rα [A,B] Rα Rβ,
```

which is also universally equal to the correct sandwich under the inverse laws.
It is therefore not a valid negative control. Swapping only one inverse pair is
genuinely false and is used instead.

Norm preservation also does not imply order independence: every ordered product
of unitary factors is unitary, while different orders can yield different
unitaries when generator commutators are nonzero.

## Evidence classification

- **Exactly derived by Julia:** Gaussian-rational Pauli instances, inverses,
  chronological products, vector checks, defect witnesses, finite exhaustive
  searches, and adversarial examples in the certificate.
- **Numerically tested by Julia:** Float64 factors/products in dimensions 2–4
  using the Euclidean induced operator 2-norm and an independently fixed
  `1e-10` limit.
- **Formally verified by Lean:** the universal finite-dimensional implications
  above. Lean does not import or trust the Julia certificate.
- **Informally interpreted:** relevance to splitting methods, coupled PDE
  discretizations, and finite-dimensional quantum evolution.
- **Not verified / out of scope:** infinite-dimensional operators, convergence
  to continuous evolution, BCH/Magnus error estimates, nonlinear flow isometry,
  and floating-point long-time conservation guarantees.
