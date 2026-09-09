# Experiment 003 — frozen Step-1 specification

Frozen at `2026-09-06T10:53:19Z` under a single four-hour authorization ending
`2026-09-06T14:53:19Z` (`06:53:19–10:53:19 EDT`). Context compaction and progress
updates do not restart this interval.

## Scope

Only **Step 1: Euclidean Resolvent Contraction** is authorized. For

```text
n : Nat
E := EuclideanSpace Complex (Fin n)
A : Matrix (Fin n) (Fin n) Complex
alpha : Real
hA : A.IsHermitian
```

reuse `NDEAEvolve.Exp002.cayleyD`, `cayleyR`, and `cayley`; represent matrix action
with `Matrix.toEuclideanCLM`; and prove the following in the norm on
`E →L[Complex] E`:

1. Resolvent averaging:
   `Rhat = (1 / 2 : Complex) • (ContinuousLinearMap.id Complex E + Chat)`.
2. Pointwise nonexpansiveness:
   `∀ x : E, ‖Rhat x‖ ≤ ‖x‖`.
3. Induced Euclidean operator-norm contraction:
   `‖Rhat‖ ≤ 1`.

Here `Rhat` and `Chat` are exactly the continuous-linear-map actions of
`cayleyR A alpha` and `cayley A alpha`. The statement must cover every real `alpha`,
including zero and negative values, and every `n`, including `n = 0`.

The proof must derive averaging from the Experiment 002 inverse/affine identities,
transport it to continuous linear maps, use scalar norm homogeneity and the vector
triangle inequality together with the inherited Cayley norm-preservation theorem, and
then use the pinned Mathlib operator-norm API. The desired contraction may not be
assumed as a hypothesis, and the resolvent may not be replaced by an unrelated map.

No strict-contraction or universal norm-equality claim is authorized. No new spectral
decomposition, functional calculus, ODE, or positivity development is in scope. The
imported Experiment 002 invertibility proof already depends on positivity; no broader
dependency claim is made.

## Required focused controls

Positive instantiations:

- `alpha = 0`;
- the zero generator;
- a negative real `alpha`.

Mathematical negative controls, each paired with a compiling positive witness:

1. In dimension one, `A = 0`, `alpha = 1`: the resolvent is the identity, so a
   uniform strict bound `‖Rhat‖ < 1` is false.
2. In dimension one, `A = i/2`, `alpha = 1`: the denominator is `1/2`, the resolvent
   is `2`, and `‖Rhat‖ ≤ 1` is false without Hermiticity.

A parser/import/timeout/tactic failure is not a mathematical rejection.

## Assurance and non-goals

- No `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` proof shortcut.
- Inspect exact signatures and transitive axioms; only subsets of `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.
- Preserve attributable command records, exit codes, timings, hashes, focused controls,
  a qualifying verbose build, predecessor checks, manifest, fresh-extraction check,
  Git bundle, archive, and adjacent receipt.
- Cache reuse is permitted but is not a clean rebuild.
- No Julia execution is required; Julia is not to be installed if absent.
- Steps 2–5 (order-defect bound, splitting defect, telescoping, and continuous
  exponential work) remain **NOT STARTED**.
- Verso, inverse-integrator, QGI, publication, and any other campaign remain
  **NOT STARTED**.

This file is the immutable Step-1 target contract. Mutable progress belongs in
`STATE.md` and must not be added retroactively to historical manifests.
