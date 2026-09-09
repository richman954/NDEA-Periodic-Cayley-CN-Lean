# Experiment 014 mathematical design review

This is a source/API design note for the active implementation, not a proof
completion receipt. Experiments 010–013 and the pinned Mathlib source were
read; no predecessor source was modified.

The preferred route is the interaction picture on weighted absolutely
summable Fourier coefficients. It directly matches the second-moment
regularity used in Experiment 010 and can conclude the actual classical
predicate of Experiment 013. A periodic L² bounded-perturbation construction
would require additional Fourier-transform, generator-domain, strong-group,
and regularity-lifting infrastructure. The bounded search of the pinned
Mathlib analysis tree found no ready analytic C₀-semigroup bounded-perturbation
theorem. This is an API assessment, not a claim that the L² route is impossible.

## Concrete target

Let H be a complex Hilbert space and w(m)=(1+|m|)² for m in Z. Assume

- sum_m w(m) norm(a_m) is finite for the initial Fourier coefficients;
- sum_j w(j) norm(v_j) is finite for bounded operators v_j on H;
- v_{-j}=v_j* so that V(x)=sum_j exp(i j x) v_j is self-adjoint.

Construct a solution on all real times to

    i u_t = -u_xx + V(x)u,      u(0,x)=sum_m exp(i m x) a_m,

periodic with period 2π, with jointly continuous u,u_t,u_x,u_xx and actual
derivatives. Then use Experiment 013 to obtain uniqueness among all solutions
satisfying that classical predicate. The initial implementation uses static
potentials and zero forcing. The bounded convolution construction supports
infinite spatial mode mixing; a finite trigonometric nonconstant potential is
already a nontrivial example, because its repeated action generates new modes.

This is a genuine infinite-mode existence theorem under explicit regularity
assumptions. It would not prove existence for arbitrary measurable potentials,
all L² initial data, nonlinear PDEs, or all systems described by Experiment
013's conditional interface.

## Construction and reusable interfaces

Store b_m=w(m)a_m in the existing complete space `lp (fun _ : ℤ => H) 1`.
Recover a_m by multiplying the stored coordinate by 1/w(m). The free phase
S(t)b_m=exp(-i m²t)b_m is an isometry and is strongly continuous.

For each j and operator A, the weighted shift

    R_j(A)b_m = (w(m)/w(m-j)) A(b_(m-j))

has operator norm at most w(j) norm(A). Therefore the series of continuous
linear maps C_v=sum_j R_j(v_j) converges in operator norm. Its decoded
coefficient is the required convolution sum_j v_j(a_(m-j)). This shift-wise
construction avoids a full two-dimensional Young inequality proof.

The interaction variable q(t)=S(-t)b(t) satisfies

    q'(t) = -i S(-t) C_v S(t) q(t).

The vector field is uniformly Lipschitz in q and continuous in t for every
fixed q. `Analysis/ODE/PicardLindelof.lean`, structure `IsPicardLindelof`,
requires exactly this separate time continuity, a uniform state Lipschitz
constant, and a local norm bound. `Analysis/ODE/ExistUnique.lean` supplies local
Picard-Lindelöf existence and interval uniqueness. The all-real-time extension
of this strongly continuous bounded linear field is a separate reusable
lemma; it is not supplied automatically by the local existence statement.

The current `GlobalLinearEvolution.lean` draft chooses a Dyson series of
iterated interval integrals instead of gluing local Picard solutions. The
bound on its nth term is `(K*|t|)^n/n! * norm(x₀)`, and a summable derivative
majorant on every bounded time interval supports actual differentiation for
all positive and negative times. This avoids a separate continuation theorem.
Consult `ODE_API_REVIEW.md` and the accepted Lean receipts for the eventual
implementation status.

## Issues the implementation must avoid

1. S(t) is not operator-norm continuous. Its conjugation of a nonzero Fourier
   shift can also fail operator-norm continuity, because the phase difference
   oscillates arbitrarily fast at high frequencies. Strong time continuity
   plus a uniform norm bound is sufficient for the ODE interface.
2. The physical weighted state b(t)=S(t)q(t) need not be differentiable in the
   second-moment norm. Its time derivative is naturally in unweighted ℓ¹.
   Requiring differentiability in the stronger norm would silently introduce
   fourth-moment regularity. Instead differentiate the free flow after
   bounded Fourier synthesis, then use a strong-operator product rule for
   varying q(t).
3. Continuity of q into ℓ¹ on a compact time interval does not by itself imply
   that the coordinatewise time suprema have a summable series. Thus a
   coordinatewise Weierstrass majorant cannot be inferred from a norm bound
   alone. Bounded synthesis maps and joint continuity avoid this issue.
4. Proving the coefficient ODE is insufficient: the endpoint must identify the
   synthesized potential multiplication with convolution, establish actual
   time and spatial derivatives, and fill every field of the Exp013 predicate.
5. Self-adjointness is used for the classical uniqueness/mass endpoint; bounded
   linear evolution itself does not require it. The development should retain
   that distinction in theorem hypotheses.

Possible later extensions are continuously time-varying weighted potential
coefficients and continuous forcing in the same weighted state space. They
need their own global evolution and synthesis hypotheses; they are not part
of the initial static homogeneous endpoint merely because the local APIs are
compatible with them.

## Draft closure review

The drafts `ScalarSeries`, `FourierSynthesis`, `StrongOperatorDerivative` and
`ClassicalExistence`, together with `MATHEMATICAL_DERIVATION.md`, were reviewed
against these interfaces. No mathematical blocker was found. The free-flow
time derivative is `i*synthSecond`; the interaction contribution is `-i*V*u`.
The classical endpoint establishes joint continuity of every actual derivative
and requires `RegularPotential` before asserting the PDE. The final unique
existence statement compares against every Exp013 classical solution with
the same initial field, rather than only comparing Fourier-constructed paths.
This source review does not substitute for the pending accepted compiler and
combined-check receipts.
