# Experiment 003 Step-1 evaluation

Status: **IN-TREE VERIFICATION GREEN — FINAL DELIVERY IS A SEPARATE OUT-OF-TREE GATE**.

The terminal in-tree status follows the successful qualifying target build,
focused controls, signature/dependency audit, prohibited-construct scan,
predecessor post-check, and evidence reconciliation. `FINAL_SHA256SUMS` is the
final in-tree mutation before release commit/tag and packaging. Fresh delivery
verification is necessarily recorded afterward in an adjacent, out-of-tree
receipt and does not rewrite this report.

## FORMALLY VERIFIED IN NEW LEAN SOURCE

The pinned Lean 4.31.0 target compiled these declarations from production source
SHA-256 `19d6ffadd0e134f0becb39d6838335455409730b4683e7a408e03f9825861bd2`:

1. `cayleyR_toEuclideanCLM_eq_average`: for any finite `n`, real `alpha`, and
   Hermitian complex matrix `A`, the Euclidean continuous-linear-map resolvent is
   one half of identity plus the Cayley map.
2. `cayleyR_toEuclideanCLM_apply_norm_le`: its action on every Euclidean vector
   has norm at most the input norm.
3. `cayleyR_toEuclideanCLM_opNorm_le_one`: its induced norm on
   `EuclideanSpace Complex (Fin n) ->L[Complex] EuclideanSpace Complex (Fin n)`
   is at most one.

The assumptions cover `n = 0`, alpha zero, and negative alpha. No strict
contraction or universal equality-to-one statement is claimed. The successful
named-target build exited 0 after `3211.401704511998` seconds using compatible
cache reuse; it is not represented as a clean rebuild or root-target build.

The exact signature/axiom audit passed. Each headline theorem depends only on
the allowed standard set `[propext, Classical.choice, Quot.sound]`.

## INHERITED VERIFIED RESULTS

Experiment 002 supplies denominator invertibility, the inverse law, the affine
Cayley identity, and Euclidean norm preservation for Cayley transforms. Step 1
reuses these results and does not claim to have re-proved the immutable release.
Its commit, annotated tag, selected Git objects, source files, dependency pins,
archive, and bundle passed the 61/61 predecessor post-check.

## MATHEMATICAL CONTROLS

The successful production target compiled the required alpha-zero,
zero-generator, and negative-alpha examples plus positive witnesses that:

- zero generator at alpha one has resolvent equal to identity, refuting a
  uniform strict-contraction claim;
- the one-dimensional non-Hermitian generator `i/2` at alpha one has an
  invertible denominator and resolvent action by two, refuting contraction when
  Hermiticity is omitted.

One separate Lean process tested both corresponding deliberately false claims.
It exited naturally with code 1; the fail-closed runner classified exactly 2/2
unique cases as attributable proposition-level type mismatches and exited 0.
Positive witnesses and rejection diagnostics are kept distinct.

## PYTHON ASSURANCE AND ARTIFACT CHECKS

- production prohibited-token scan: PASS, zero matches;
- signature/axiom parser on the successful source-bound log: PASS;
- assurance-tool self-check after its documented parser repair: 13/13 PASS;
- predecessor immutability: 61/61 PASS;
- build input identities before/after: byte-identical.

The first signature-parser attempt and first post-repair self-check failed for
documented, attributable reasons. Both failures and the narrow Python-only
repairs are preserved. No production theorem, statement, assumption, or proof
was changed during this assurance repair.

## COMPUTATION

No fresh Julia or numerical computation was executed for this corollary. The
result is a new formal norm estimate derived from inherited exact structure, not
a claim of fresh Julia discovery.

## NOT VERIFIED / OUT OF SCOPE

- strict contraction for all Hermitian generators;
- contraction without Hermiticity;
- Steps 2–5 of the campaign;
- order-defect norm bounds, splitting defects, telescoping/global convergence,
  or continuous-exponential comparison;
- Verso, inverse-integrator, or QGI work;
- a clean-cache or clean-runtime replay;
- human peer review or independent external review (PENDING).

Archive hashing, Git verification, and fresh extraction establish artifact
identity and consistency; they are not described as a new Lean proof replay.
