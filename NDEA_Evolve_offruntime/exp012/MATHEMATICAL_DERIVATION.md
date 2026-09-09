# Classical periodic uniqueness for the concrete spinor equation

The equation is `i ∂t u = −∂xx u + V u`, with `V=Z+X`,
`Z=diag(1,−1)` and `X` swapping the two spin components. The period is `2π`.
The two split potentials do not commute, while their sum is Hermitian.

The solution class is exactly the predecessor's
`Exp010.IsClassicalPeriodicSolution`: actual first time, first space and second
space derivatives exist everywhere; the solution and those derivatives are
jointly continuous; the function is spatially periodic; and the actual
derivatives satisfy the pointwise equation. The new proof does not replace
this predicate or add a Fourier representation, energy conservation premise,
or global time bound for a competing solution.

## Local identity

The complex inner product is linear in its second argument. Write

```text
ρ(t,x) = ‖u(t,x)‖²,
D(t,x) = 2 Re ⟨u(t,x), ∂t u(t,x)⟩,
J(t,x) = 2 Re ⟨u(t,x), i ∂x u(t,x)⟩.
```

The actual time derivative of `ρ` is `D`. Rearranging the PDE gives
`∂t u = i ∂xx u − i V u`. Hermitian symmetry makes `⟨u,V u⟩` real,
so `Re ⟨u,−i V u⟩=0`. Also `Re ⟨∂x u,i ∂x u⟩=0`.
Differentiating the inner product in `J` therefore proves `∂x J=D`.
Our convention is `∂tρ=∂xJ`; `J` has the opposite sign from the current in
`∂tρ+∂xj=0`.

Differentiating the actual identity `u(t,x+2π)=u(t,x)` gives periodicity
of the spatial derivative. Thus the flux is periodic as well. This boundary
fact is proved rather than added to the solution predicate.

## Integral conservation

For an arbitrary real base `b`, define

```text
E_b(t) = ∫[b,b+2π] ρ(t,x) dx.
```

To differentiate at an arbitrary time `t`, joint continuity of `D` bounds
its absolute value on the compact rectangle
`[t−1,t+1] × [b,b+2π]`. A constant integrable majorant on this rectangle
allows differentiation under the integral over a neighborhood of `t`.
This supplies a local bound from the existing hypotheses; it does not assume
a bound uniform over all times.

The fundamental theorem of calculus and periodic flux then give

```text
E_b′(t) = ∫[b,b+2π] D(t,x) dx
        = J(t,b+2π)−J(t,b) = 0.
```

Consequently `E_b(s)=E_b(t)` for all real times `s,t`, including negative
times, and every real interval base.

## Separation and uniqueness

The original classical predicate is closed under subtraction. For arbitrary
classical `u,v`, apply conservation to `w=u−v`. Their squared period L²
distance is exactly conserved. If they agree at any one time, that distance
is zero at every time and on every interval of length `2π`.

For a continuous spinor function `f`, a nonzero value at `x` makes
`∫[x,x+2π] ‖f(y)‖² dy` strictly positive. The interval-integral positivity
theorem includes a positive value at an endpoint. Zero energy on all such
intervals therefore implies `f=0`. Choosing the interval base at each spatial
point avoids quotient representatives or modular reduction of coordinates.
This proves equality of the two functions for all real times and positions.

## Existence and numerical limit

For coefficients satisfying `Σ_m (1+|m|)² ‖a_m‖<∞`, the predecessor already
constructed a global classical periodic solution `U_a`. Uniqueness now shows
there exists exactly one classical solution with initial values `U_a(0,x)`.
This is existence for the stated regular Fourier initial data, not existence
for arbitrary initial functions.

Every other classical solution with those data equals `U_a`. Experiment 011's
uniform convergence theorem and explicit error bound therefore apply to that
unique solution. The actual numerical reconstruction, exact sampled
initialization, closed space-time rectangle `[0,1] × [0,2π]`, and refinement
schedule are unchanged. No sharper rate or weaker-data result is inferred.

The final [completion report](COMPLETION_REPORT.md) records acceptance of the
source checks. [Reproduction instructions](REPRODUCE.md) and the
[saved-file guide](SAVED_FILES.md) identify the evidence and trusted inputs.
