
# Julia → Lean evidence map and trust boundary

## What Julia did

`sources/julia/discover_fourier_stability.jl` constructs the stencil Laurent
polynomial over `Rational{BigInt}`, multiplies its exact factors, performs the
half-angle coefficient rewrite after explicitly named standard analytic identities,
constructs the Cayley numerator/denominator over `Complex{Rational{BigInt}}`,
checks the scalar cross-multiplication certificate, and derives both norm-squared
polynomials as `1+a^2`. It also reconstructs four exact rational samples and five
adversarial witnesses.

Its machine-readable artifact is `certificates/fourier_certificate.json`, run ID
`exp001-61dea9a49a42-20260905115957`, source SHA-256 `20ee35c97ef47dc05a4b684630d1df4d519b3bc1a85984d914c4e027c6d49410`, certificate SHA-256
`d842fc370f19f588cef2bbf5c824c00f4527918ac76073aadc86087080f326cc`, and canonical core SHA-256
`61dea9a49a42448b89a8358b1c099a1c1630464f38363bd676ebb7d441106d04`.

The independent Python assurance layer `sources/tools/validate_certificate.py`
does not accept stored Booleans alone. It reparses rational coefficients, rebuilds
the Laurent product, half-angle coefficient calculation, structured Cayley solve,
cross multiplication, norm products, four rational samples, canonical core hash,
and all five named adversarial witnesses. Its exit code is `0`.

## What Lean did independently

`sources/lean/FourierStability.lean` imports Mathlib but imports no Julia artifact.
Lean independently proves the complex phase identities, sine-square stencil symbol,
local Fourier-neighbor eigen-relation, eigenvalue nonnegativity under `h != 0`,
Cayley denominator nonvanishing for real `a`, the scalar update equation, and unit
modulus. The headline theorem is
`NDEAEvolve.Exp001.cayleyCN_fourier_mode_stability` with `h > 0`.

## Trust statement

- Julia's `overall_status` Boolean is not a Lean premise.
- Lean does not parse the JSON certificate.
- Python validation is an assurance layer, not part of Lean's trusted kernel.
- The cross-language correspondence is transparent definitions, paths, and hashes;
  it is not a formal semantics theorem connecting Julia execution to Lean syntax.
- Standard trigonometric identities used as analytic interpretation are separately
  re-proved in Lean.

The Julia attempt-005 classification overstated exactness for two floating-point
witnesses. The peer audit repaired that in attempt 006 using exact Laurent evaluation
at `z=-1`, exact Gaussian rationals, structured certificates, and a stronger validator.
Both the superseded and repaired artifacts/diagnostics are preserved.
