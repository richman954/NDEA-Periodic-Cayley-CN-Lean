# Disposition of two specification edge cases

## Unconditional norm-one wording

The preferred route asks for `‖S_hat‖ = ‖U_hat‖ = 1` unconditionally. This is
false when the matrix dimension is zero: `E 0 →L[ℂ] E 0` is the trivial
operator algebra, so its identity operator and every Cayley operator have norm
zero. Mathlib correspondingly requires `[Nontrivial E]` for
`CStarRing.norm_of_mem_unitary`.

The release retains the universal matrix dimension by using the stronger
operational fact needed by the proof: left or right multiplication by a
unitary preserves the middle operator norm. The relevant Mathlib lemmas require
no nontriviality assumption, so every telescoping summand has exactly the local
defect norm even in dimension zero. In positive dimension, the familiar
norm-one equalities follow as usual.

## The requested `N^2` trap

An upper bound proportional to `N^2` is not false merely because the optimal
bound is linear. For every natural `N>=1` and every nonnegative `delta`,

`N * delta <= N^2 * delta`.

Consequently the verified linear fan bound entails the quadratic upper bound.
Lean records this in `linear_bound_implies_n_squared_bound`.

The requested strict example is still meaningful as a sharpness control, not
as a counterexample to the upper bound. The compiled exact witness has local
error `1/10` and two-step error `19/100`, strictly below the quadratic
allowance `2/5`. No false counterexample was fabricated.
