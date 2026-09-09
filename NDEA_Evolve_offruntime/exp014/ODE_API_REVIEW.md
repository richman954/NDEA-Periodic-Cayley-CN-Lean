# Pinned Mathlib ODE existence API review

The pinned library supplies Banach-space local existence with the required
time-continuity assumptions. It does not supply a directly applicable global
existence theorem for a merely strongly continuous, time-dependent linear
operator. A new continuation/gluing argument is needed, or a new Picard
fixed-point construction on an arbitrary compact interval.

This is source inspection, not a compiled new proof. Mathlib is pinned to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; exact inspected source hashes are
in `ODE_API_REVIEW_SOURCES.json`. No predecessor files were changed.

## Public local existence interface

Import `Mathlib.Analysis.ODE.ExistUnique`. The relevant typeclasses are
`[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`. A complex Banach
space can use its induced real scalar structure; time differentiation is real.

The global namespace structure `IsPicardLindelof`, defined in
`Analysis/ODE/PicardLindelof.lean:86`, has the following exact fields:

```lean
IsPicardLindelof (F : ℝ → E → E)
  (t₀ : Set.Icc tmin tmax) (x₀ : E) (a r L K : ℝ≥0)

lipschitzOnWith : ∀ t ∈ Set.Icc tmin tmax,
  LipschitzOnWith K (F t) (Metric.closedBall x₀ a)
continuousOn : ∀ x ∈ Metric.closedBall x₀ a,
  ContinuousOn (F · x) (Set.Icc tmin tmax)
norm_le : ∀ t ∈ Set.Icc tmin tmax,
  ∀ x ∈ Metric.closedBall x₀ a, ‖F t x‖ ≤ L
mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r
```

Here `L` bounds the vector field, and `K` is its Lipschitz constant. They are
different parameters. The displayed coercions in the last line are to reals.

`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, at
`Analysis/ODE/ExistUnique.lean:71`, has this interface:

```lean
(hf : IsPicardLindelof F t₀ x₀ a 0 L K) :
  ∃ α : ℝ → E, α t₀ = x₀ ∧
    ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt α (F t (α t)) (Set.Icc tmin tmax) t
```

The version without the terminal subscript zero, at line 57, takes arbitrary
`r` and `hx : x ∈ Metric.closedBall x₀ r`, and returns initial value `x`.
The returned function has values on all real numbers, but its ODE is asserted
only on the specified closed interval. Those outside values do not establish
global existence.

On the open interior, convert with
`hα t htIcc |>.hasDerivAt (Icc_mem_nhds ht.1 ht.2)`. The same file's local
flow theorem at line 114 also supplies joint continuity in initial data and
time. Its `ContDiffAt` convenience existence theorems are autonomous and
require C¹; they are unnecessary for the desired continuous-time linear ODE.

## Strong continuity supplies the needed compact bounds

Let `A : ℝ → E →L[𝕜] E`, where `𝕜` can be real or complex, and assume
`∀ x, Continuous (fun t => A t x)` and `Continuous f`. On a compact interval J:

1. `isCompact_Icc.exists_bound_of_continuousOn` bounds `‖A t x‖` uniformly
   over `t ∈ J` for each fixed x. The generated additive theorem is documented
   at `Analysis/Normed/Group/Bounded.lean:96`.
2. Apply `banach_steinhaus` to the family indexed by the subtype `J`. Its exact
   relevant type, from `Analysis/Normed/Operator/BanachSteinhaus.lean:36`, is
   `(∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) → ∃ C', ∀ i, ‖g i‖ ≤ C'`, with complete
   domain E. Thus strong continuity yields a uniform operator-norm bound K
   on each compact time interval. Operator-norm continuity is not required.
3. Bound f on J by the same compact-continuity theorem, obtaining F₀ ≥ 0.
   Bounds may be replaced by their maximum with zero before using `ℝ≥0`.
4. `ContinuousLinearMap.lipschitzWith_of_opNorm_le`, an alias at
   `Analysis/Normed/Operator/Basic.lean:343`, converts `‖A t‖ ≤ K` into
   `LipschitzWith K (A t)`. Adding the fixed value `f t` leaves the constant
   unchanged; this can also be shown directly from `map_sub` and the norm bound.
5. The PL time-continuity field only needs each fixed-x slice. Joint
   continuity follows, when needed, from
   `continuousOn_prod_of_continuousOn_lipschitzOnWith'` at
   `Topology/EMetricSpace/Lipschitz.lean:510`. The primed form puts time in
   the first factor and the Lipschitz variable in the second factor.

For the interaction-picture Fourier route, this distinction matters: a free
group may be strongly continuous while failing operator-norm continuity.
The local PL API does not force the stronger, unsuitable assumption.

## Viable extension argument to prove

The following is a proposed proof route, not an existing Mathlib theorem.
For `F(t,x)=A(t)x+f(t)`, on a fixed compact time slab with bounds K,F₀ ≥ 0,
choose at every initial state x₀

```text
a(x₀) = ‖x₀‖ + F₀ + 1
L(x₀) = (2K+1) a(x₀)
ε = 1/(2K+1).
```

For `‖x-x₀‖ ≤ a`, one has `‖x‖ ≤ 2a` and `F₀ ≤ a`, so
`‖A(t)x+f(t)‖ ≤ (2K+1)a = L`. Therefore `L ε = a`. Local existence
holds for a common positive time radius ε independent of x₀, wherever
the symmetric time interval remains inside the slab. Use a slightly larger
compact slab around the target interval to retain endpoint margins.

Glue overlapping local solutions to reach any prescribed compact interval.
The uniform time radius avoids a separate bound on the growing solution
norm. Then choose compatible solutions on expanding intervals centered at
the initial time; uniqueness gives a global function that locally agrees
with one selected interval solution. Transfer its derivative through this
local equality. This last exhaustion step follows the pattern of
`isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo`, but should be proved
directly with `HasDerivAt` and the nonautonomous uniqueness theorem below.

`ODE_solution_unique_of_mem_Ioo`, at `Analysis/ODE/ExistUnique.lean:279`, takes

```lean
(hv : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (v t) (s t))
(ht : t₀ ∈ Set.Ioo a b)
(hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
(hg : ∀ t ∈ Set.Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
(heq : f t₀ = g t₀) : Set.EqOn f g (Set.Ioo a b)
```

Take `s t = Set.univ`. This accepts a different K for each compact interval.
The convenient `ODE_solution_unique_univ` at line 341 instead requires one
K for all time; do not introduce that extra global bound merely to use it.
For endpoints, `ODE_solution_unique_of_mem_Icc` at line 252 needs continuity
on Icc and actual derivatives only on its interior. Right/left initial-time
variants are at lines 194 and 209.

## Alternatives and limitations

The existing global extension theorem
`exists_isMIntegralCurve_of_isMIntegralCurveOn`, in
`Geometry/Manifold/IntegralCurve/UniformTime.lean:162`, requires an autonomous
vector field with `CMDiff 1`. Augmenting the state by time does not satisfy
that assumption for merely strongly continuous A and continuous f. Its
gluing proof is a useful model, not a directly applicable theorem.

Alternatively, define the Picard operator on the complete space
`C(Set.Icc a b, E)` and prove its n-th iterate has Lipschitz bound
`(K * max (b-t₀) (t₀-a))^n / n!`. Then
`ContractingWith.isFixedPt_fixedPoint_iterate`, at
`Topology/MetricSpace/Contracting.lean:316`, turns any contracting iterate
into a fixed point of the original Picard map. This avoids small-time gluing
inside a compact interval, but requires a new integral operator and its
factorial estimate. Existing `ODE.FunSpace` estimates are implementation
details tied to the bounded-ball PL structure and cannot simply remove its
time constraint.

The most direct new endpoint is existence and uniqueness of a global real-time
solution of `u'=A(t)u+f(t)` for strongly continuous bounded operators and
continuous forcing on a Banach space. That endpoint still needs an actual
Lean implementation; the source inspection above does not establish it.

## Implemented homogeneous uniform-bound endpoint

`lean/GlobalLinearEvolution.lean` now constructs the homogeneous evolution
using the Dyson series. It passed the modular Lean check recorded in
`evidence/20260908T153640.533133Z_GlobalLinearEvolution.json` (exit 0,
196.497 seconds). `evidence/GLOBAL_LINEAR_EVOLUTION_CHECK.json` binds the
accepted source, compiler log, artifact and ten public declarations. Four
cosmetic unused-section-variable warnings remain. Combined axiom audits are
still pending at this checkpoint.

The accepted endpoint is `NDEAEvolve.Exp014.exists_global_linear_solution`:

```lean
(A : ℝ → E →L[ℝ] E)
(hA : ∀ x, Continuous (fun t => A t x))
(K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) :
  ∃ u : ℝ → E, u 0 = x₀ ∧ ∀ t, HasDerivAt u (A t (u t)) t
```

The actual constructed function is `linearEvolution A x₀`. The proof covers
all real times using factorial bounds on actual iterated interval integrals
and locally uniform derivative bounds for the series. It neither assumes a
solution nor assumes a fixed point. It does not yet implement the more
general forcing/compact-bound endpoint discussed in the API review above.
