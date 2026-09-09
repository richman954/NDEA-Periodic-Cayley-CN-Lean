# Independent statement of the Exp016 target

Specification review, September 9, 2026 UTC. This document states the intended
numerical/PDE claim from the authorized PLAN and sealed APIs; it is not a Lean
proof or a claim that the current implementation meets the target. Independence
here means separation of the target statement from the new implementation's
proofs, not independent authorship or independent runtime qualification.

The baseline is the actual periodic Schrödinger problem

    i ∂t u = −∂xx u + V(x)u,     u(0,x)=u₀(x),     period 2π,

with fiber H=ℂ². Write u₀(x)=Σ_m exp(imx)a_m and
V(x)=Σ_l exp(ilx)V_l. The intended baseline data assumptions are exactly
Σ_m(1+|m|)²‖a_m‖<∞, Σ_l(1+|l|)²‖V_l‖op<∞ and V_{−l}=V_l*.
The reference is Exp014's constructed `solution`, using `ofCoefficients` for
the datum, and its proved classical solution/uniqueness properties. These are
not new existence assumptions supplied by the numerical implementation.

## Actual discretization and independent reconstruction

For every M≥0, put N=2M+1, h=2π/N, x_j=jh, and use the sealed full-grid state
space `SpinorGrid.Vec (SpinorGrid.Grid (2*M))`, namely the Euclidean norm on
Fin N × Fin 2. Grid vectors carry unweighted Euclidean norm; physical size is
√h‖y‖. Every matrix norm in a quantitative bound is the induced Euclidean
operator norm, not an unspecified default matrix norm.

Keep the old centered periodic stencil and the actual sampled potential:

    (L_h y)_j = (2y_j−y_{j+1}−y_{j−1})/h²,
    A_h = L_h⊗I + I⊗Z,             Z=diag(1,−1),
    (B_h y)_j = (V(x_j)−Z)y_j,     H_h=A_h+B_h.

Indices wrap modulo N. The old `PeriodicGrid.laplacian`,
`SpinorGrid.hamiltonian` and `potential` are the definition anchors. The new
sampled block operator must be proved to have precisely this action and to be
Hermitian. For constant V=Z+X its B_h must equal the sealed `potential (2*M) X`;
the whole numerical step must then equal the old `SpinorGrid.symmetric`.

For each positive step k_j, use the sealed inverse Cayley factor
C_G(a)=(I−iaG)(I+iaG)⁻¹ and the ordered stages

    y₁=C_A(k_j/4)y_j,
    y₂=C_B(k_j/2)y₁,
    y_{j+1}=C_A(k_j/4)y₂.

This is A-half/B-full/A-half in actual action order. There is no commuting
hypothesis and no replacement by a single C_{A+B}(k_j/2). Exact inverse
arithmetic is the baseline; floating-point solves require a separate validated
solve-error interface.

Define the full centered DFT and its physical reconstruction directly:

    â_m(y) = N⁻¹ Σ_{r=0}^{N−1} exp(−imx_r)y_r,    −M≤m≤M,
    S_h y(x) = Σ_{m=−M}^M exp(imx) â_m(y).

Required identities are sampling fidelity at every node, actual first and
second derivatives, 2π-periodicity, and
‖S_h y‖_{L²(b,b+2π)}=√h‖y‖ for every b and every grid vector. This is the
unnormalized interval integral, not the old piecewise spatial reconstruction
and not a supremum-norm comparison.

Let t₀=0, t_{j+1}=t_j+k_j. For one slab, abbreviate the actual endpoints by
y₀,y₃, set m=(y₀+y₃)/2, v=(y₃−y₀)/k, s=t−(t_j+k/2), and define

    c(t)=(i/2)(s²−k²/4),
    Q_j(t)=m+s v−c(t)H_h v,       w_j(t,x)=S_h Q_j(t)(x).

Each polynomial extends to all real t; it must independently satisfy the
sealed Exp015 regular-field predicate. Its endpoints must equal S_h y_j and
S_h y_{j+1}. Agreement of time derivatives between neighboring slabs is neither
required nor asserted.

## Certificate target, with every defect retained

For arbitrary stage values define the actual denominator residuals

    r₁=y₁−y₀+i(k/4)A(y₁+y₀),
    r₂=y₂−y₁+i(k/2)B(y₂+y₁),
    r₃=y₃−y₂+i(k/4)A(y₃+y₂),
    η=(y₁+y₂−y₀−y₃)/2,          d=i v−H_h m.

The required exact identity is d=(i/k)(r₁+r₂+r₃)+(A/2+B)η.
Exact stages cancel the three r terms; they need not cancel η or d. For exact
stages the stronger identity must retain order:

    η=(k²/32)A²(y₀+y₁+y₂+y₃)+(k²/8)AB(y₁+y₂).

Define the actual continuum spatial discrepancy, with its sign fixed by the
PDE above,

    C_h z = S_h(H_h z)+∂xx(S_h z)−V S_h z.

The required residual is the actual derivative expression
R_V[w]=i∂t w+∂xx w−Vw, and its identity is

    R_V[w_j](t)=S_h d+c(t)S_h(H_h²v)+C_h Q_j(t).

The primary analytical slab budget is the explicitly defined nonnegative
quantity

    β_j=√h(‖d‖+k_j²‖H_h²v‖/8)
        +‖C_h m‖L²+(k_j/2)‖C_h v‖L²+(k_j²/8)‖C_h(H_h v)‖L².

Prove ‖R_V[w_j](t)‖L²≤β_j on the whole closed slab. Expose both stencil and
sampled-potential interpolation/aliasing terms in C_h; a structure field named
"consistency" does not establish those equalities or estimates. Exact-stage
coarser bounds, with a=‖A_h‖op and b=‖B_h‖op, are

    ‖d‖≤(k²/16)a(a+2b)²‖y₀‖,
    ‖H_h²v‖≤(a+b)³‖y₀‖.

An integrated correction constant k³/12 may sharpen the uniform k³/8
certificate, but must be proved for the same actual reconstruction.

The end-to-end certificate must quantify over every finite number J of slabs,
all positive step lengths, all M≥0, every datum/potential in the stated class,
and **arbitrary numerical y_initial**. Its grid-time conclusion is

    ‖S_h y_n−u(t_n)‖L² ≤ ‖S_h y_initial−u₀‖L² + Σ_{j<n} k_j β_j,
    for every 0≤n≤J.

For a final partial slab t∈[t_n,t_{n+1}], the target is

    ‖w_n(t)−u(t)‖L² ≤ ‖S_h y_initial−u₀‖L²
                        +Σ_{j<n}k_jβ_j+(t−t_n)β_n.

These statements use one fixed actual classical reference on all slabs.
They do not apply Exp015 globally to a stitched non-C1 path. J=0 retains the
initial mismatch exactly; zero step lengths are excluded wherever division by
k or endpoint recovery needs k≠0.

## Eventual convergence target and quantifiers

The baseline qualitative goal is convergence for **each fixed** admissible
(a,V) and each fixed finite horizon T>0. The first proposed family is
N_q=2(q+1)+1, h_q=2π/N_q, J_q=N_q⁴, k_q=T/J_q; PLAN's first test horizon is
T=1. Initialize by the actual samples
y_q⁰(j)=u₀(jh_q), using the sealed `Exp010.sampleSolution` convention, and run
the actual stages above. The direct certificate route proves that the initial
interpolation error and accumulated actual defect budgets vanish as q→∞. The
density/stability route can instead close the error target from certificates
on each fixed smooth approximant, without requiring the rough datum's own
high-graph-norm certificate terms to vanish. The required conclusion is

    max_{0≤n≤J_q} ‖S_{h_q}y_q^n−u(nk_q)‖L² → 0.

The continuous-time version concerns the just-defined slab reconstruction and
requires the corresponding partial-slab bound uniformly on [0,T]. If only
grid-time convergence is proved, say so. No rate O(h²+k²), uniform operator
norm convergence over all L² data, or theorem for arbitrary independently
shrinking h and k is implied by this particular refinement family.

Proving convergence first for a stronger, explicitly stated smooth class is a
valid intermediate result, not completion for all Exp014 data. The proposed
density/stability route must first prove actual-scheme convergence for each
fixed smooth approximant, then transfer it by mesh-independent initial-data
and potential-perturbation estimates. Fix the approximant before taking the
mesh limit, and only then remove the approximation. Smooth finite Fourier
inputs do not make the variable-potential evolved solution finite-band.
No premise that these same residual budgets tend to zero can substitute for
that derivation. The time schedule only suppresses the coarse temporal
h-dependent constants after the needed uniform sampled-potential and initial
weighted-norm bounds are proved; it says nothing by itself about spatial error.

## Definition-binding payoff and adversarial review

`lean/IndependentTarget.lean` defines the raw DFT/quadratic
reconstruction directly from sealed predecessor APIs, without importing the
new Exp016 implementation. Required connecting theorems must identify the
implementation's sampled operator, actual iterates and reconstructed field
with those definitions, then establish its regularity, actual residual and
the stated certificate for that identified field. Merely instantiating a
generic conditional error interface does not complete this connection.

The initial certificate is analytical. Its exact-real integrals, infinite
Fourier data/tails and matrix inverses are not automatically computable
certified numbers. Validated arithmetic, quadrature and effective tail bounds
are additional interfaces needed for such a numerical certification claim.

Adversarial checks before any full-target label:

- Preserve noncommuting action order and the AB term; exact solves can have a
  nonzero unsplit midpoint defect even when A and B commute.
- Full centered high modes violate the old |m|h≤1 small-band hypothesis.
  L² isometry/unitarity controls mass, not derivative or high graph norms.
- Point sampling is not uniformly bounded on arbitrary L² equivalence
  classes; use the actual regular Fourier data assumptions and prove tails.
- Retain numerical initialization mismatch, all three solve residuals for
  inexact stages, and the actual sampled-vs-continuum potential discrepancy.
- Check normalization N⁻¹, √h, period 2π, negative frequencies, N=1,
  wraparound indexing, both slab endpoints and the final partial interval.
- Do not infer global C1 gluing from matching endpoint values, make residual
  smallness an input to a claimed convergence theorem, or hide additional
  smoothness, h/k restrictions or constants depending on the refinement.
- Use a nonzero one-node spinor with V=2cos(x)I: sampling gives 2I whereas the
  constant reconstruction's spatial discrepancy is (2−2cos x)u. Exact stage
  solves cannot erase this actual continuum mismatch.

Authoritative anchors: PLAN.md; NUMERICAL_PINS.json;
exp008/lean/Exp007Foundation.lean and FourierGrid.lean;
exp010/lean/ClassicalClosure.lean (`sampleSolution`);
exp011/lean/Reconstruction.lean (`nodeValue`, historical reconstruction);
exp014/lean/WeightedFourier.lean, FourierPotential.lean and ClassicalExistence.lean;
exp015/lean/ResidualField.lean, SpatialL2.lean and ResidualEstimate.lean.
New proof-module counts and acceptance receipts are deliberately not premises
of this target specification.
