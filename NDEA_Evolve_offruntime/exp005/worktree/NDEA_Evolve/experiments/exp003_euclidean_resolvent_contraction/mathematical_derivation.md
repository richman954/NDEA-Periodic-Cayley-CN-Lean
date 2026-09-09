# Step-1 mathematical derivation

Let

\[
X=i\alpha A,\qquad D=I+X,\qquad R=D^{-1},\qquad
C=(I-X)R.
\]

For a finite complex Hermitian matrix `A` and real `alpha`, Experiment 002 already
proves both that `D R = I` and that `C` preserves the standard Euclidean norm. Its
invertibility proof uses positivity; Step 1 does not replace or bypass that inherited
argument.

From `D R = I`, the inherited purely algebraic affine identity gives

\[
C=(I-X)R=2R-I.
\]

Rearranging over the complex scalars gives the exact averaging formula

\[
R=\tfrac12(I+C).
\]

Transport this matrix equality through `Matrix.toEuclideanCLM`. For every vector
`x` in `EuclideanSpace Complex (Fin n)`, norm homogeneity, the triangle inequality,
and the inherited equality `||C x|| = ||x||` yield

\[
\begin{aligned}
\|Rx\|_2
 &= \tfrac12\|x+Cx\|_2 \\
 &\le \tfrac12(\|x\|_2+\|Cx\|_2) \\
 &= \|x\|_2.
\end{aligned}
\]

The defining upper-bound property of the continuous-linear-map operator norm then
gives

\[
\|R\|_{2\to2}\le 1.
\]

No sign condition on `alpha` occurs, and the argument remains valid when `alpha = 0`
and when `n = 0`. It proves a non-strict upper bound, not universal equality.

## Boundary controls

- With `n = 1`, `A = 0`, and `alpha = 1`, `R = I`, so its operator norm is exactly
  one. This refutes a uniform strict-contraction claim.
- With `n = 1`, `A = (i/2)I`, and `alpha = 1`, `D = (1/2)I` and `R = 2I`. This
  generator is not Hermitian and the resolvent operator norm is two, showing that the
  Hermiticity premise cannot simply be omitted.

These are exact examples. No numerical experiment or fresh Julia execution is used
in this corollary.
