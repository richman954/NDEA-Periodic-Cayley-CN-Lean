# Experiment 002 — evaluation report

Status: **IN-TREE VERIFICATION GREEN; OUTER DELIVERY STATUS IS EXTERNAL**. All
frozen mathematical, witness, rejection-control, signature/axiom,
forbidden-token, root-build, and predecessor-immutability gates are hash-bound
below. This immutable report does not self-attest the archive containing it;
final local-closure status belongs to the adjacent off-runtime delivery receipt
and timestamped closure report. External human review is **PENDING**.

## Claim-status table

| Claim class | Status | Evidence boundary |
|---|---|---|
| Universal finite-dimensional Lean theorems | PASS | Kernel-checked sources plus signature/axiom audit |
| Exact Julia reconstruction and certificate | PASS | Exact Gaussian-rational run plus independent strict validator |
| Numerical matrix trials | PASS as bounded observations | Float64 tests, never promoted to proof |
| Positive/counterexample witnesses | PASS | Complete verbose target build |
| Seven false Lean controls | PASS, 7/7 rejected | Independently reclassified bound raw diagnostics |
| Final root target | PASS with cache reuse | Complete verbose log and role metadata |
| Outer archive/bundle/fresh extraction | See adjacent receipt | Cannot be self-attested inside the immutable archive |
| External human review | PENDING | Not replaced by local assurance |

## Mathematical scope and conventions

For `A : Matrix (Fin n) (Fin n) ℂ` and `α : ℝ`, the experiment defines

```text
Dα(A) = I + i α A,     Nα(A) = I - i α A,
Rα(A) = Dα(A)⁻¹,       Cα(A) = Nα(A) Rα(A),
[P,Q] = P Q - Q P.
```

Every product retains its written noncommutative order. A chronological list
`[U₁,U₂,U₃]` denotes `U₃ U₂ U₁`, so the head step acts first.

## FORMALLY VERIFIED

Lean 4.31.0 has independently kernel-checked the following universal
finite-dimensional results; none imports or trusts the Julia certificate.

- `cayleyD_isUnit` and `cayleyD_det_ne_zero`: Hermiticity of `A` and a real
  parameter imply that `Dα(A)` is invertible and has nonzero determinant.
  Invertibility is derived through positive-definiteness of `Dα(A)†Dα(A)`, not
  assumed in the Hermitian headline.
- `cayley_unitary`, `cayley_preserves_inner`, and `cayley_preserves_norm`:
  `Cα(A)` is two-sided unitary and preserves the standard complex Euclidean
  inner product and norm.
- `orderedCayleyProduct_unitary`,
  `orderedCayleyProduct_preserves_inner`, and
  `orderedCayleyProduct_preserves_norm`: any finite ordered list of changing
  Hermitian generators with changing real steps has a unitary, norm-preserving
  product. No pairwise commutativity premise is used. The list is an
  exogenously fixed realized sequence; this does not establish distance
  preservation for a state-dependent nonlinear choice of generators.
- `cayley_order_defect`: assuming the four explicit two-sided inverse laws for
  the two denominators, but not Hermiticity,

  ```text
  [Cα(A),Cβ(B)]
    = (-4 * (α : ℂ) * (β : ℂ)) •
        (Rα(A) Rβ(B) [A,B] Rβ(B) Rα(A)).
  ```

- `cayley_commute_iff_of_inverse_laws`: under those inverse laws and
  `α ≠ 0`, `β ≠ 0`, the Cayley factors commute exactly when the generators do.
- `hermitian_cayley_commute_iff`: for Hermitian generators and `αβ ≠ 0`, the
  same equivalence holds with the inverse laws derived internally.

The exact positive-witness module additionally proves order sensitivity for
Pauli generators, detects the wrong defect sign and a one-sided inverse
permutation, and supplies counterexamples to dropped Hermiticity, a complex
step, omission of the nonzero-step condition, and false semigroup merging.
Its complete verbose target build returned 0 after 8,559 jobs. The source
SHA-256 is
`ef71de8e6a7188aec8df817550fe848048358268cb1a2e63f4ba4be4b002dd17`;
the 568,743-byte log SHA-256 is
`71f8725f733879403b58e0635f68736196fd083538358e40e271acc7c35eb0ad`.

## EXACTLY DERIVED BY JULIA

Julia 1.12.6 used exact Gaussian-rational matrix arithmetic to reconstruct
Pauli generators; Cayley denominators, numerators, inverses, and factors;
chronological products; nine exact vector norm-squared preservation checks; and the ordered
commutator-defect formula. It checked six edge cases, eleven exact adversarial
examples, and all 81 real `2 × 2` matrices with entries in `{-1,0,1}`.

The finite search found two singular denominators after Hermiticity was dropped
and 52 invertible non-Hermitian examples with nonunitary Cayley factors. These
are exact bounded computations, not universal proofs.

The machine-readable certificate is
`certificates/operator_cayley_core.json`, SHA-256
`a80cfd44b43e69131c7e5e63576362767b8ca6a4406e1c7c4ccc83edfa0c4120`.
The independent Python validator accepted 3/3 valid configurations, rejected
31/31 unique altered fixtures in 34 total invocations, and performed 530 checks
in its strongest configuration. The validator is an assurance layer, not part
of Lean's trusted proof base.

## NUMERICALLY TESTED

With seed `20260905`, Julia tested Float64 matrices of dimensions 2, 3, and 4
using the Euclidean induced operator 2-norm: 4,608 individual factors and 1,536
ordered three-factor products. Maximum residuals were approximately
`6.65e-15` and `7.16e-15`, respectively, against an independently fixed
`1e-10` acceptance limit. These observations are not proofs, convergence
estimates, or long-time error bounds.

## INFORMALLY INTERPRETED

The results motivate later work on finite-dimensional splitting methods,
coupled discretizations, graph evolution, and quantum dynamics. Those
connections are interpretations, not additional theorems established here.

## NOT VERIFIED / OUT OF SCOPE

This experiment does not prove results for unbounded or infinite-dimensional
operators, convergence to continuous evolution, BCH/Magnus estimates, PDE
well-posedness, state-dependent nonlinear flow isometry, floating-point
long-time conservation, or order independence of noncommuting factors. It does
not substitute an entrywise matrix norm for the Euclidean induced norm and does
not claim novelty for the classical Cayley identities. QGI, inverse-integrator,
topology/geometry, and legacy-restore work are outside this mission.

## Assurance gates

- Seven false Lean controls: **PASS**, 7/7 unique cases from one stable-source
  Lean invocation. Lean returned the required natural exit code 1 after
  2,972.770 seconds; the strict runner returned 0. All seven diagnostics were
  independently reclassified as exact attributable type mismatches, with no
  timeout, import/infrastructure error, malformed source, extra diagnostic, or
  mixed witness. Full runner log/results SHA-256:
  `2f41d35b7783d465f3b647da0c46ffb1078adad3aa8d753aef771eeb232ddb9a`;
  raw merged diagnostic SHA-256:
  `01dfdde30701a90376d2ecc24bb7e1806c8139b7104698812b5c211f4148e7dd`.
- Declaration signatures and transitive axiom audit for 17 frozen declarations:
  **PASS**, Lean exit 0. All signatures were printed; the axiom union is exactly
  `[propext, Classical.choice, Quot.sound]`, with zero unexpected axioms and zero
  forbidden dependencies. Full Lean log SHA-256:
  `4b868d6ff164a57e7a30922ca3a76c1d62518679000052a202f5f58b404cba6a`.
  Parsed result SHA-256:
  `26c1a85b74071369c1418af42b7edca249184ae1ed7a6344ed670b2dfb5fdf5d`.
- Production forbidden-token scan for `sorry`, `admit`, custom `axiom`,
  `unsafe`, and `native_decide`: **PASS**, zero matches in both production Lean
  files; its final role metadata is hash-bound. Inclusion in the final manifest
  remains part of preclosure.
- Required final verbose root Lake build: **PASS**, exit 0 after
  `2846.7023403430067` seconds, 8,562 jobs. The 571,938-byte complete log has
  SHA-256
  `68f96ab17c5934ce18b41cc17991bb4ec6849d2b16103921339eb14592f4f8b7`.
  The default target imported `NDEAEvolve.Basic`,
  `NDEAEvolve.Experiments.Exp002.OperatorCayley`, and
  `NDEAEvolve.Experiments.Exp002.AdversarialWitnesses`, then built the
  `NDEAEvolve` root. This was an incremental build with compatible cache replay,
  not a clean-runtime recompilation. Unimported audit/control units retain their
  separately bound checks.
- Historical Julia-green manifest compatibility: **PASS after a preserved
  repair**. A preclosure check exposed only the later-mutated `STATE.md` entry
  (67/68). Its newer bytes were preserved additively, the historically bound
  path was restored exactly, and the postcheck passed 68/68. No historical
  manifest or mathematical artifact changed.
- `FINAL_SHA256SUMS` is generated as the last in-tree content mutation and is
  committed with the selected tree. Its own hash, the annotated tag object,
  archive, Git bundle, and independent fresh-extraction results are recorded
  outside the immutable tree by the adjacent delivery receipt and closure
  report.
- Experiment 001 archive/tag/subtree immutability: preflight and renewed-window
  post-checks **PASS**. The post-check also revalidated both assurance-v2
  artifacts and its local verification receipt.
- Durable off-runtime milestones: preflight, Julia-green, strengthened-witness,
  assurance-harness, axiom-audit, and negative-controls-green checkpoints are
  **PRESERVED**. The final delivery is authoritative only when its adjacent
  off-runtime verifier receipt records PASS.

The final fresh-extraction verifier will audit archive safety, hashes,
manifests, Git bindings, evidence semantics, and a fresh Python certificate
regression replay. It does not rerun Lean or Julia; their archived executions
remain distinguished as direct execution evidence.

## Toolchain pins

- Julia `1.12.6`
- Lean `4.31.0`, commit `68218e876d2a38b1985b8590fff244a83c321783`
- Lake `5.0.0-src+68218e8`
- elan `4.2.4` (`227caca13`)
- `lean-toolchain`: `leanprover/lean4:v4.31.0`
- Mathlib revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

Experiment 001 remains immutable; its release-archive sentinel is
`131a89fc12a0f7ae71011c50af7e359fd9c3f8ebbb974c982f77f9309c4127aa`.
Experiment 001 assurance-v2 and Experiment 002 both retain external-review
status **PENDING**.

The contradiction among the earlier recorded authorization deadline, inferred
command start, completion timestamp, and elapsed duration remains unresolved;
the original records were not changed. The earlier continuation used
`metadata/renewed_authorization_window_20260905.json`. This finalization and its
root build were governed by the distinct three-hour window
`metadata/finalization_authorization_window_20260906.json`, from
`2026-09-06T05:55:29.913656550Z` through
`2026-09-06T08:55:29.913656550Z`.
