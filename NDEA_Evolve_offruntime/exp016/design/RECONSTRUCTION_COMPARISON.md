# Exp016 reconstruction comparison and proposed endpoint

Design review only. The identities below are mathematical derivations to
formalize; this document reports no Exp016 Lean acceptance. Exp015's accepted
50-audit final verification and sealed packet were read before this review.

## Recommendation

Use a regular spatial synthesis and a **quadratic time reconstruction on each
slab**, with the affine reconstruction retained as its elementary precursor.
Derive the defect from the actual three Cayley stages. The selected Exp016
target includes **full odd-grid Fourier interpolation, its exact L2 norm
isometry, and sampled variable potentials**. Use the existing finite-band,
constant-matrix-potential spinor recurrence as an early concrete consumer and
control. The full-grid interface then covers arbitrary initial grid vectors
and keeps their initial mismatch explicit without changing the energy argument.

Do not require the piecewise assembled field to satisfy Exp015's global
regularity predicate. Each slab is the restriction of a globally defined
polynomial-in-time regular field. Apply Exp015 separately on each slab and add
the results. Value jumps contribute their L2 sizes; derivative jumps contribute
no extra term in this argument. This makes no distributional-derivative claim.

## What the existing source actually supplies

- `exp015/lean/ResidualField.lean` defines actual first time and first/second
  spatial derivatives, joint continuity of all four fields, and periodicity.
  Its residual is `i*w_t + w_xx - V*w`. `ResidualEstimate.lean` derives the
  error bound from these hypotheses and retains the initial error.
- `exp008/lean/Exp007Foundation.lean`, lines3153–3157 and3406–3408, retains
  the actual definitions `den(a,H)=1+i*a*H`, `num(a,H)=1-i*a*H` and
  `symmetric=C_A(k/4) C_B(k/2) C_A(k/4)`. Application starts at the rightmost
  factor. Here `A=op(hamiltonian n h K)` and `B=op(potential n Q)`;
  `hamiltonian` includes the positive discrete minus-Laplacian and `K`.
  Existing `potential n Q` is spatially constant, not a sampled variable field.
- `exp008/lean/StageBridge.lean` connects actual denominator residuals and
  the full-grid three-stage budget to finite Fourier coefficients. Exact
  numerical stages have zero denominator residual. The reference endpoint
  used in its consistency theorem is a different object from a numerical
  endpoint with zero stage-solve error.
- `exp008/lean/FourierGrid.lean` proves sampling/intertwining and preservation
  of a finite Fourier superposition by the constant-potential split scheme.
  `Orthogonality.lean` proves **discrete** orthogonality/Parseval on an alias-free
  band. It does not yet provide inverse DFT for every grid vector or continuum
  L2 Parseval for a new interpolation operator.
- `exp009`–`exp012` close the established constant-matrix-potential Fourier
  problem through regular infinite data, classical solutions and uniqueness.
  `exp011/lean/Reconstruction.lean` evaluates actual grid iterates using
  clamped floor indices in both space and time. This piecewise constant field
  generally fails Exp015's differentiability and continuity hypotheses.

## Serious alternatives

| Reconstruction | Fidelity and regularity | Norm, aliasing and order | Lean cost and decision |
|---|---|---|---|
| Existing piecewise constant field | Exact saved numerical output; discontinuous at generic cell/slab interfaces | Existing pointwise transfer loses a factor `1/sqrt(h)`; cannot be inserted into classical residual theorem | Keep as a later output-transfer target, never assert it is classically regular |
| Trigonometric synthesis + affine time | Spatially smooth and periodic; exact slab endpoints; grid-node fidelity requires sampling/inversion proof or an already tracked finite band | Transparent spatial aliasing; residual contains `-tau*H*v`, whose L1 time estimate can lose the second-order temporal rate | Lowest-cost regular baseline; prove its basic field/derivative lemmas and reuse them |
| Trigonometric synthesis + quadratic time | Same endpoint values; correction is a global polynomial on each slab | Actual endpoint defect plus a `k^2/8` temporal residual term; no assumption that splitting defect vanishes | Recommended: modest polynomial/linear-map algebra above affine, substantially stronger certificate |
| Trigonometric synthesis + cubic Hermite time | Exact state endpoints and chosen slopes `-i*H*Uj`; fixed-grid slabs can join with a continuous time derivative | Can preserve temporal accuracy, but its residual has additional endpoint-defect/operator terms; all must be derived | Viable global-C1 alternative. Formal piecewise gluing and interval indexing add cost; reuse the quadratic construction first and revisit if global smooth output becomes a concrete consumer |
| Exact semidiscrete flow `S(exp(-i*(t-t_n)*H_h) U_n)` | Smooth interior, starts at the numerical state; generally does **not** end at the next Cayley state | Interior temporal defect is zero, but the endpoint jump is the full exponential-versus-split-step defect; spatial commutator remains | Useful later alternative; exponential regularity and local step estimates add cost without eliminating consistency work |
| Continuous rational Cayley stage path | `C_A(s/4) C_B(s/2) C_A(s/4) U_n` matches both endpoints and uses the actual method | Derivative has resolvent/product/noncommutator terms; selfadjointness makes real-parameter denominators invertible | Faithful but more derivative and cancellation machinery than a polynomial; not the first choice |
| Periodic C2 local spline/Hermite synthesis | Can interpolate grid values; ordinary piecewise linear or merely C1 reconstructions are insufficient | Avoids Fourier aliasing, but needs uniform reconstruction stability and a new stencil-versus-second-derivative estimate; arbitrary smoothing does not preserve nodes | Serious future local-mesh branch; existing Fourier infrastructure makes it more expensive now |

Affine interpolation of accurate nodal values may itself be second-order
accurate. The issue is that integrating its residual **norm** can discard the
cancellation needed to prove that order; no contradiction is intended.

A cubic Hermite path deserves separate consideration from spatial splines. For
fixed H, choose both endpoint slopes from `-i*H*Uj`; they agree across adjacent
slabs, so a global C1 path is mathematically available. This does not avoid
proving endpoint defects or spatial consistency. It adds a piecewise-gluing
proof and extra residual terms. The chosen slabwise quadratic route directly
uses Exp015 on arbitrary intervals and already avoids derivative-jump claims.
It is also a useful precursor: its endpoint derivative differs from the desired
slope by `-i*d` at both ends. An endpoint-vanishing cubic correction can later
repair those slopes. This is an opened construction, not a checked theorem or
an asserted rate.

## Exact split-stage identity: first reusable theorem

Let `k>0`, and let `A,B` be complex linear operators on a grid Hilbert space.
Write the successive stage states as `U0,U1,U2,U3`, and define the actual
denominator residuals, including any solve error,

```text
r1 = U1-U0 + i*(k/4)*A(U1+U0)
r2 = U2-U1 + i*(k/2)*B(U2+U1)
r3 = U3-U2 + i*(k/4)*A(U3+U2)
H  = A+B
m  = (U0+U3)/2
v  = (U3-U0)/k
eta = (U1+U2)/2 - m
d  = i*v - H*m.
```

Summing these exact definitions gives

```text
d = (i/k)*(r1+r2+r3) + (A/2+B)*eta.                 (1)
```

This identity needs only linearity and `k≠0`. No commutation or stability
assumption is needed. It is compatible with the saved stage order and the
existing `gridFactorResidual` definition. For exact numerical stages `rj=0`,
the generally nonzero term `(A/2+B)*eta` remains. Even commuting `A,B` do not
make a product of Cayley factors equal to one unsplit CN factor.

For the physical grid norm `||z||_h=sqrt(h)*||z||`, (1) immediately bounds
the solve contribution by `gridStageBudget/k` in the existing `K=Z,Q=X`
instance. The stage-geometry term is additional; it is not already a zero
solve residual or a supplied consistency hypothesis.

For exact stages, put `aj=Uj-U(j-1)`. A second useful exact identity is

```text
eta = (i*k/8)*A(a1+2*a2+a3)
    = (k^2/32)*A^2(U0+U1+U2+U3)
      + (k^2/8)*A*B(U1+U2).                       (2)
```

The order `A*B` is intentional. With Hermitian `A,B`, saved stage unitarity
gives `||Uj||=||U0||` and, writing `a=||A||, b=||B||`,

```text
||eta|| <= (k^2/8)*a*(a+2*b)*||U0||
||d||   <= (k^2/16)*a*(a+2*b)^2*||U0||.           (3)
```

Retaining the norms of the actual `A^2 Uj`, `AB Uj`, and then
`(A/2+B)A^2 Uj`, `(A/2+B)AB Uj` from (2) gives a stronger graph-norm
certificate than replacing every operator by its norm. With inexact stages,
the intermediate identity gains `(r1-r3)/2`; do not reuse exact-stage
unitarity without accounting for solve errors.

## Quadratic field and its actual PDE residual

Let `tau=t-(t_n+k/2)` and define, for every real `t`,

```text
Q(t) = m + tau*v - (i/2)*(tau^2-k^2/4)*H*v.
```

Then `Q(t_n)=U0`, `Q(t_n+k)=U3`, and direct differentiation gives

```text
i*Q'(t)-H*Q(t) = d + (i/2)*(tau^2-k^2/4)*H^2*v.  (4)
```

Thus the grid residual is bounded on the slab by
`||d|| + (k^2/8)||H^2 v||`. Its temporal-correction integral has the sharper
constant `k^3/12`. For exact stages, the elementary norm estimate
`||H^2 v|| <= (a+b)^3 ||U0||` also follows from the three jump bounds.

For a fixed regular spatial synthesis `S`, define
`L_V w = -w_xx + V(x)w` and the **calculated** spatial discrepancy
`Cz = S(H z) - L_V(S z)`. The physical field `W(t,x)=S(Q(t))(x)` has residual

```text
R_V[W](t) = S(d) + (i/2)*(tau^2-k^2/4)*S(H^2 v) + C(Q(t)).   (5)
```

For sampled-grid `H=L_h+P_V`, the spatial term separates exactly into

```text
Cz = [S(L_h z) + (S z)_xx] + [S(P_V z) - V*S z].
```

These are the stencil/synthesis discrepancy and potential interpolation/
aliasing discrepancy. Neither is assumed zero. A time-dependent potential
would add its actual time dependence to this expression; static potentials
are the first numerical target.

Exp015 and the elementary spatial L2 triangle/homogeneity lemmas then yield
the concrete one-slab certificate

```text
error(t_n+k) <= error(t_n)
  + k*||S(d)||L2 + (k^3/12)*||S(H^2 v)||L2
  + integral_[t_n,t_n+k] ||C(Q(t))||L2 dt.          (6)
```

Using `k^3/8` from the pointwise bound is an acceptable first checked version;
the `1/12` polynomial integral is an optional inexpensive sharpening. Initial
mismatch stays explicit. A finite slab theorem adds actual interface value
jumps, which are zero for matching endpoint reconstructions on one fixed grid.

## Suggested Lean API and honest Exp016 boundary

Suggested theorem sequence, not existing declarations:

1. `split_endpoint_defect_eq_stage_residuals`: (1), specialized immediately
   to the saved `step(k/4) A`, `step(k/2) B`, `step(k/4) A` recurrence.
2. `split_stage_geometry_eq` and `split_endpoint_defect_norm_le`: (2)–(3),
   keeping graph-norm and simpler operator-norm versions separately.
3. `quadraticSlab_endpoints`, `quadraticSlab_hasDerivAt`,
   `quadraticSlab_residual`: (4), including nonzero actual endpoint defect.
4. A small `RegularSynthesis` interface with evaluation, first derivative and
   second derivative maps `x -> G ->L[complex] H`, actual derivative identities,
   spatial continuity and periodicity. This avoids introducing a new Banach
   space of C2 functions. Finite-grid trigonometric synthesis satisfies these
   explicit conditions by finite sums.
5. `synthesized_quadratic_regular`, `synthesized_quadratic_residual` and
   `quadraticSlab_error_to_classical`: actual Exp015 regularity, (5) and (6).
   Add spatialL2 triangle/homogeneity and finite-slab accumulation as reusable
   prerequisites, rather than silently assuming an L2 norm API already exists.

The selected endpoint is this reusable certificate **plus full odd-grid DFT
interpolation and its L2 norm isometry, instantiated for the actual sampled
variable-potential split recurrence**. This is larger than a finite-band-only
endpoint, but it closes a shared reconstruction bottleneck and supports
arbitrary initial grid mismatch. Inverse DFT and continuum finite-sum Parseval
are substantive new milestones; existing discrete Parseval alone does not
establish either the full interpolation interface or its continuum norm.

An early finite-band consumer of the saved noncommuting spinor split scheme
checks endpoint sampling and the explicitly calculated nonzero splitting
defect. Existing `symmetric_pow_superposition` gives numerical fidelity for
that constant-potential invariant band. A single-mode instance is a useful
exact control, not the full intended endpoint. Finite-band acceptance alone
must not be reported as completion of the selected full-grid target.

For arbitrary grid vectors and spatially variable sampled potentials, use a
complete integer-frequency representative set. Odd grid size `N=2M+1` is a
clean first convention: inverse DFT/sampling and exact
`||S z||L2=sqrt(h)||z||` must be proved. Variable potential generally destroys
an undersampled invariant low band, so old band preservation cannot be reused.
The full representative band also does not satisfy the old small-band condition
`M*h<=1` as `N` grows; do not silently apply that consistency theorem to it.

Full variable-potential convergence can honestly be a separate Exp017:
potential aliasing bounds, high-frequency control, uniform graph norms and
refinement schedules remain after Exp016's inverse DFT and norm transfer.
The valid fixed-grid bound (3) has constants growing like powers of `h^-2`;
an `O(k^2)` label at fixed grid is not a mesh-uniform convergence rate. The
Exp015 regularity class alone does not supply the higher derivatives needed
for proposed uniform second-order time or space bounds. Any stronger data/
potential assumptions must be explicit and their persistence proved.

## Assessment of the consolidated PLAN

The chosen operators `A_h=L_h+Z`, `B_h=sample(V)-Z` sum to the required
`H_h=L_h+sample(V)` and recover the saved `Z/X` split when `V=Z+X`.
The quadratic correction has the stated sign, exact endpoint values and
`k^2/8` pointwise temporal constant. Expanding the linear spatial discrepancy
along the quadratic field gives precisely the PLAN's three terms
`||C_h m||L2 + (k/2)||C_h v||L2 + (k^2/8)||C_h(H_h v)||L2`.
No mathematical flaw was found in this proposed certificate.

For the proposed later schedule `N=2q+3`, `h=2*pi/N`, `k=N^-4`, the crude
temporal budget is `O(k^2*h^-6)=O(N^-2)` only after proving uniform bounds
both on the sampled potential operator norm and on the initial physical grid
norm `sqrt(h)*||y0||`. Stage unitarity propagates the latter but does not
create it for arbitrary families of initial grid vectors. Neither this
schedule nor the L2 isometry implies that the spatial discrepancy tends to
zero. Higher graph-norm estimates are not consequences of an L2 isometry.

The full-grid target is a sound Exp016 boundary, with a real formalization
cost concentrated in inversion, continuum Parseval and the concrete regularity
consumer. Acceptance of the first algebra modules is a useful startup
milestone, not completion of that boundary. As a minor comparison detail,
an exact semidiscrete-flow alternative needs exponential machinery; a matrix
logarithm is needed only for a different construction that embeds an entire
numerical step as an exact autonomous flow.
