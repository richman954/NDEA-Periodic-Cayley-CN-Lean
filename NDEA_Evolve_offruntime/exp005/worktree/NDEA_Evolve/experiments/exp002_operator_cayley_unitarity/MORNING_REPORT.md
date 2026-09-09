# NDEA-Evolve overnight morning report

Generated: 2026-09-05 (America/New_York)

## Exp001 assurance-hardening v2

Status: CLOSED LOCALLY; EXTERNAL HUMAN REVIEW PENDING.

- Evidence archive:
  `/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2_evidence.tar.gz`
- Archive SHA-256:
  `3f460ecd7f88de93bc403ae2371601686a083dcba911b05f6784464114f719be`
- Git bundle:
  `/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/Exp001_Assurance_Hardening_v2.bundle`
- Bundle SHA-256:
  `fb8cb79fc574522fdb142b348b50637087c75e582f437ed19531260546ad5257`
- Local delivery receipt:
  `/home/richman954/NDEA_Evolve_offruntime/exp001/assurance_v2/local_v2_delivery_verification.json`
- Receipt SHA-256:
  `62a02d08b0dcb873ffba905622803e2e27ce7dd6695bf8a4f426391d8e466556`
- Commit: `813f866d...`; tag:
  `exp001-assurance-hardening-v2-verified-20260905`.
- Result: original valid certificate unchanged and accepted in required
  configurations; 293/293 altered executions rejected across 61 unique invalid
  fixtures; fresh-extraction replay passed.

## Experiment 002: Audited Noncommutative Cayley Composition

Overall status: PARTIAL. Julia-green is closed. The universal Lean core is
kernel-checked, but full Lean assurance closure has not yet been claimed.

### Frozen objectives

- [x] Preserve and replay verified preflight.
- [x] Julia exact matrix reconstruction and certificate generation.
- [x] Julia numerical counterexample/search layer, explicitly non-universal.
- [x] Strict independent matrix-certificate validator and altered fixtures.
- [x] Universal finite-dimensional Hermitian denominator invertibility in Lean.
- [x] Universal single-factor two-sided unitarity in Lean.
- [x] Universal standard Euclidean inner/norm preservation in Lean.
- [x] Ordered variable-step, changing-generator product unitarity/norm
  preservation in Lean with no pairwise commutativity assumption.
- [x] Exact noncommutative order-defect identity in Lean.
- [x] Nonzero-step Cayley commutation iff generator commutation in Lean.
- [ ] Integrated positive-witness build closure (the core subtarget passed;
  witness compilation was interrupted at the time ceiling without a result).
- [ ] Seven attributable Lean rejection-control executions.
- [ ] Captured declaration/signature and transitive axiom audit.
- [ ] Final warning-clean verbose production build and manifest.
- [ ] Lean-green, preclosure, and final durable delivery.

### Exact declarations already proved by the universal core

The core has passed a remote direct check, a remote verbose Lake build, and a
local direct check after style cleanup. Its headline declarations include:

- `cayleyD_isUnit`, `cayleyD_det_ne_zero` — finite Hermitian denominator
  invertibility for real steps;
- `cayley_unitary`, `cayley_preserves_inner`, `cayley_preserves_norm` —
  two-sided unitarity and standard Euclidean preservation;
- `orderedCayleyProduct_unitary`,
  `orderedCayleyProduct_preserves_norm` — chronological products for arbitrary
  lists of changing Hermitian generators and real steps, with no commutativity
  assumption;
- `cayley_order_defect` — exact ordered identity
  `[Cα(A),Cβ(B)] = -4 α β · Rα Rβ [A,B] Rβ Rα`, under explicit two-sided
  denominator inverse laws and no Hermiticity assumption;
- `cayley_commute_iff_of_inverse_laws` — commutation equivalence under the four
  inverse laws and `α ≠ 0`, `β ≠ 0`;
- `hermitian_cayley_commute_iff` — Hermitian corollary deriving inverse laws and
  taking the explicit assumption `α * β ≠ 0`.

The matrix/norm in the preservation theorem is Mathlib's
`Matrix.toEuclideanCLM` acting on `EuclideanSpace ℂ (Fin n)`, not an entrywise
surrogate norm.

### Julia and validator closure

- Julia-green commit: `0e913e9cadd5c25ff9c982c5be373cbe38618c50`.
- Julia certificate SHA-256:
  `a80cfd44b43e69131c7e5e63576362767b8ca6a4406e1c7c4ccc83edfa0c4120`.
- Exact layer: three Pauli instances, nine vector checks, 81 search cases, two
  singular cases, 52 non-Hermitian/nonunitary cases, and 11/11 adversarial
  witnesses.
- Numerical layer: 4,608 single-factor and 1,536 product checks; maximum
  residuals approximately `6.65e-15` and `7.16e-15`, under the independently
  fixed limit `1e-10`.
- Independent validator: 530 exact/schema checks; 3/3 valid executions
  accepted; 31/31 unique altered fixtures rejected; 34 process invocations.
- Julia-green bundle SHA-256:
  `43ac78ec6db3f303731549d889e7c07a4d7f2d3484885f3615d7860ecf841a22`.
- Julia-green archive SHA-256:
  `b0232f826c94e02eef203ca4f7fcbd60d65b7078e810af074b9146a875d93121`.
- Fresh extraction, 68/68 manifest entries, Git tree comparison, and regression
  replay all passed.

### Lean evidence and controls

- Remote direct attempt 5: PASS, exit 0. Its reconstructed source matches the
  remote-recorded source SHA-256 exactly:
  `19de0fa01d1a51397e55604ecefc5ff30c282aa018adb8d38af5b89959c09d09`.
- Remote verbose core build: PASS, exit 0, 8,558 jobs, 58.777 seconds.
- Full remote verbose log recovered byte-for-byte from durable local CLI
  history; SHA-256:
  `2eae3878f600b44ee9f6263e789e246f2374e39c73be8ddaa48569ed38921aa5`.
- Style-cleaned core local direct check under Lean 4.31.0 and pinned Mathlib:
  PASS, exit 0; source SHA-256
  `be29c41df0bd17e977c9e12d7a81e348be3deb6cf7e64b67a117aa6cc3722a54`.
- Production forbidden-token scan: PASS over both staged production files.
- Positive witness source SHA-256:
  `85d7c457e7773a285d9673750aaff288eb7572b46b605142841c22f0c44cded8`.
- Bounded local verbose integrated attempt: the cleaned core subtarget passed in
  2,808 seconds; the process was sent SIGINT at the authorized ceiling while the
  witness compilation remained silent. This is recorded as `NOT_OBTAINED`, not
  as either witness success or mathematical failure. Full partial log SHA-256:
  `32020ded4b0cf99224675aa43e8425c804df1c9e32856b5870f7566b8e98da75`.
- Seven false-control sources and a strict runner are staged. They are not
  reported as passed until their separate nonzero exits and attributable
  diagnostics are captured.
- Axiom audit status: PENDING EXECUTION. No claim is made from source inspection
  alone.

### Failures, repairs, and mathematical lessons

- Recovered Julia draft initially aborted by applying a Hermitian-only check to
  a non-Hermitian control; checks were gated by their assumptions.
- Numerical product testing used leading blocks of differently sized unitaries
  and an unconditional PASS; it was repaired to use same-sized full factors,
  finite checks, and a fixed `1e-10` acceptance limit.
- A proposed "wrong inverse order" control reversed both inverse pairs. That is
  another universally valid factorization, not a counterexample. The control
  was replaced by a genuinely false one-sided permutation.
- An explicit scalar witness rejects the false Cayley semigroup-merging claim.
- Lean proof attempts 1–4 failed and their exact logs were recovered; attempt 5
  passed. The first witness attempt failed only because the core `.olean` did
  not yet exist, not because its mathematics was refuted.

### Runtime loss and preservation

The original endpoint was lost. Exactly one authorized standard CPU-only
replacement was created and restored from the verified Julia-green bundle. It
later returned 404/401 and lost its local name. A read-only listing showed the
same endpoint as an unidentified `?`; it was not stopped or reused. No second
replacement was created.

The byte-exact CLI history and recovery receipts are under:

`/home/richman954/NDEA_Evolve_offruntime/exp002/recovery/20260905T_second_runtime_loss/`

Latest fully packaged partial checkpoint before the bounded build outcome:

- Commit: `398d671b657ceab0a031ac8a09d266b3e36034e0`.
- Tag: `exp002-lean-core-docs-partial-20260905`.
- Bundle:
  `/home/richman954/NDEA_Evolve_offruntime/exp002/checkpoints/lean_core_partial_documented/NDEA_Evolve_exp002_lean_core_partial_documented.bundle`
- Bundle SHA-256:
  `13d13fa69ac2e06b25a54cd0820ee5a70aeb5ce5c385e407cb76ac44bd32d775`.
- Archive:
  `/home/richman954/NDEA_Evolve_offruntime/exp002/checkpoints/lean_core_partial_documented/NDEA_Evolve_exp002_lean_core_partial_documented.tar.gz`
- Archive SHA-256:
  `4c6403b9743b68c357256920e0e2c71f2f883ec4aa0e095f1bf38357cf0d1e27`.
- Receipt:
  `/home/richman954/NDEA_Evolve_offruntime/exp002/checkpoints/lean_core_partial_documented/local_partial_documented_receipt.json`.
- Bundle verification and archive safe-path inspection: PASS.

### Exact next task

Resume the cached witness target (the core `.olean` already exists locally):

```text
cd /home/richman954/NDEA_Evolve_offruntime/exp002/worktree/NDEA_Evolve
/home/richman954/.elan/bin/lake -v build NDEAEvolve.Experiments.Exp002.AdversarialWitnesses
```

If it passes, run
`experiments/exp002_operator_cayley_unitarity/controls/lean/run_negative_controls.py`,
then compile
`experiments/exp002_operator_cayley_unitarity/assurance/PrintAndAxiomAudit.lean`,
inspect its signatures/axiom sets, and perform the final verbose root build and
manifest. If the witness build fails, preserve its complete log and repair only
the isolated witness source without weakening any universal theorem.

External review of Exp002: PENDING.
