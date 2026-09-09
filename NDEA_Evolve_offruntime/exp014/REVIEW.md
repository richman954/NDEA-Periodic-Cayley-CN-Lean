# Experiment 014 final source and verification review

Reviewed on 2026-09-09 UTC. **The exact source/workflow review passes, with no
unresolved mathematical or acceptance-gating blocker identified.** This is not
a completed-experiment receipt. All nine current modular sources have accepted
Lean checks. At review completion, the local combined result also reports
success for all 143 audits in 178.418 seconds, with 10,768 external artifacts
unchanged. The independent combined, transferred-evidence, and packet
qualification remain pending. Source/tool review is distinct from those gates.

The reviewed combined source is `lean/Exp014Combined.lean`, SHA-256
`40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee`.
The catalog contains 143 new public theorem/control declarations: 121
production declarations and 22 controls. These are audit counts, not a claim
that every declaration is a distinct research contribution. The machine-readable
`evidence/REVIEW_CHECK.json` binds the exact sources, tools, documents, review
text, and prepared deliveries considered here.

## Mathematical scope

For an arbitrary complete complex Hilbert space H, integer frequencies, and
weight w(m)=(1+|m|)^2, the endpoint assumes

```text
Σ_m w(m) ‖a(m)‖ < ∞,
Σ_j w(j) ‖v(j)‖ < ∞,
v(-j) = v(j)*,
V(x) = Σ_j exp(i j x) v(j).
```

Here a(m) is H-valued and v(j) is a bounded complex-linear operator on H. The
final theorem constructs exactly one classical periodic solution of

```text
i u_t = -u_xx + V(x)u,
u(0,x) = Σ_m exp(i m x) a(m),
period = 2π,  time and position range over all real numbers.
```

Its solution predicate is the unchanged Experiment 013 classical predicate.
The theorem establishes actual first time and first/second spatial
derivatives, their required joint continuity, spatial periodicity, and the
pointwise PDE. Uniqueness compares with every function satisfying that
predicate and initial field, without imposing a Fourier representation on
the competing solution.

This is a regular linear periodic class with static operator-valued potential
and zero forcing. Rough L² data, arbitrary irregular or time-varying
potentials, nonlinear equations, other boundary conditions, and numerical
convergence for this enlarged class are outside the endpoint. No finite fiber
dimension, finite Fourier cutoff, or commutation of the potential with the
Laplacian is assumed.

## Construction and derivative closure

The weighted state stores w(m)a(m) in Mathlib's complete ℓ¹ space. The decode
and initialization identities recover the input coefficients exactly, and
the state norm equals their weighted absolute sum. The free phases define an
isometric group with strong and joint continuity. Operator-norm continuity
is not assumed.

For each operator coefficient, the weighted shift has the correct ratio
w(m)/w(m-j) and is bounded by w(j)‖v(j)‖. Regularity proves actual summability
of the shift series in operator norm. The two private `operatorSeries`
helpers instantiate standard norm-series results over abstract normed spaces;
they change elaboration cost without changing assumptions. Evaluation and
coefficient extraction commute with this convergent sum through continuous
linear maps. Single-shift synthesis is reindexed explicitly, and the full
convolution identity follows by bounded synthesis. No unsupported exchange
of an arbitrary double series is used.

The interaction generator is uniformly bounded and jointly continuous in
time and state. Its real-linear Dyson construction uses actual iterated
interval integrals and a factorial majorant. The derivative series has a
summable majorant on a neighborhood of every real time, including negative
time. This generic module supplies global ODE existence; the final PDE
uniqueness statement is supplied separately by Experiment 013.

Synthesis, first spatial synthesis, and second spatial synthesis all use
multipliers bounded by one after division by w(m). Fixed-state ℓ¹ majorants
justify differentiation. The scalar signs are correct: spatial derivatives
contribute im and -m², and the free time derivative is i times second spatial
synthesis. The strong-operator product rule then gives
u_t = i u_xx - i V(x)u. It does not require differentiability of the physical
state in the second-moment norm or an unintended fourth moment.

The private `synthesis_along_continuous_state` helper is ordinary composition
in product topologies. The final continuity fields rewrite explicitly proved
equalities between actual derivative functions and their continuous
synthesized expressions. This matches every field of the Exp013 predicate;
no separate placeholder derivative field is substituted for an actual
derivative. Initial data decode exactly at time zero, and positive period and
selfadjointness permit the retained energy-based uniqueness theorem.

Some intermediate definitions are totalized for arbitrary coefficient
sequences through Lean's `tsum`. All uses interpreting these series as the
specified Fourier potential at the PDE endpoint require `RegularPotential`.
The broader selfadjointness statement without regularity therefore does not
remove the endpoint's convergence hypothesis.

## Controls and nonvacuity

The 22 controls include signed single-mode data and its actual synthesized
field, a negative-frequency free derivative sign, regularity and Hermitian
symmetry for a two-sided nonzero potential, its values at zero and π, and
the resulting proof that the potential is nonconstant. They also establish
the zero-potential identities and a regular coefficient sequence nonzero at
every integer, with infinite support proved explicitly.

Three controls instantiate unique classical existence: variable potential
with a signed single mode, zero potential with infinite-support data, and
variable potential with infinite-support data. The final zero-potential
control proves an equality of the complete potential functions using
`funext`, then rewrites the endpoint theorem with that equality. It preserves
the exact Exp013 predicate and initial condition.

These witnesses show that the hypotheses admit nonzero data, spatially
varying potentials, and infinitely supported initial coefficient families.
The construction uses all integer Fourier modes without a finite cutoff.
The controls do not separately prove persistence or creation of infinite
coefficient support along every later-time trajectory.

## Exact inputs and verification workflow

All 13 component/provenance source hashes were freshly compared with
`FINAL_INPUTS.json`, and the combined source and complete receipt were
reconstructed exactly without modifying them. An independent direct scan of
the nine modules' public theorem declarations agrees with all 143 catalog
names and the 121/22 split. The proof-policy scan found no prohibited
placeholder or unsafe proof token. Each of the nine actual modular receipts,
its log, its unchanged source hash, and its current output artifact hash were
read back and verified. No Lean rerun was performed by this reviewer.

The three original Exp013 generic bodies remain pinned and embedded in the
combined source. Their classical uniqueness interface was inspected. Earlier
numerical proof chains are preserved outside this combined check and are not
claimed to be rechecked by it.

`INFRASTRUCTURE_REVIEW.md` records the reviewed reconstruction, isolated
external import closure, compiler/dependency pins, fresh-runtime protocol,
delivery checks, command/log checks, receiving validator, and final seal
gates. It now includes the actual prepared bootstrap launcher hash. Its
environment-isolation improvement and mode-wording clarification have been
resolved. Both prepared archives were independently read back: six bootstrap
members and 21 final-source members, with complete manifests and exact local
byte agreement. Both carry the reviewed combined source.

The prepared bootstrap archive has SHA-256
`282703ece0a48347fdedf7400fde536be5fbf33961b621a3b188fa4b5264bec0`.
The final-source archive has SHA-256
`82984ac339762e4396d4e8ca96030c358401fe97bf9d948d93e705384f42534a`.
The pinned bootstrap launcher has SHA-256
`a31fc5905109ebda7bfed760f4eb3697d7492f2e4175b89e2a4b9f6e7bc54a9e`.

The local combined result was inspected after it completed successfully.
The saved fresh-bootstrap result reports 57 successful commands. The
independent combined check must still establish successful elaboration and
the allowed axiom catalog, after which the receiving checker must accept the
independent evidence, including its full bootstrap logs. The finalizer must also
revalidate this review's exact source/tool/document hashes and predecessor
preservation before sealing. Compatible compiler and compiled external
library artifacts remain trusted inputs; neither this review nor the
workflow rebuilds Lean and Mathlib from source. Recovery snapshots and local
backups protect continuity and do not substitute for these proof receipts.
