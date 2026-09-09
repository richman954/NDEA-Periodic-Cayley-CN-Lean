# Disposition of the requested small-step scaling control

The request asked for a small-step counterexample to

`‖E_local(alpha)‖ <= 4 * |alpha| * ‖Ahat‖ * ‖Bhat‖`.

Such a counterexample is impossible under the verified theorem. If
`|alpha| <= 1`, then

`alpha^2 = |alpha|^2 <= |alpha|`.

Because both operator norms and the coefficient 4 are nonnegative, the
verified estimate

`‖E_local(alpha)‖ <= 4 * alpha^2 * ‖Ahat‖ * ‖Bhat‖`

implies the proposed `|alpha|` estimate throughout the small-step regime.
Lean certifies this implication generically in
`quadratic_bound_implies_absolute_linear_bound_of_abs_le_one` and for the
Cayley defect in `absolute_linear_bound_holds_of_abs_le_one`.

The intended global scaling trap is still valid because `alpha^2 > |alpha|`
when `|alpha| > 1`. Lean, Julia, and the Python certificate validator all check
the corrected witness `alpha = 10`, `A = B = (1/10) I_1`.

This is a mathematical correction, not an execution omission. No false witness
was fabricated, and the requested example was checked before use as required.
