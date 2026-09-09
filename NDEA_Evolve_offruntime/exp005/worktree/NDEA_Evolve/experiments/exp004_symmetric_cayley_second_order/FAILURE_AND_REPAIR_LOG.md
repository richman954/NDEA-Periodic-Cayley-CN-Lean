# Experiment 004 failure and repair record

This record is finalized with the release. Timestamped command receipts and
logs remain the primary compilation evidence, including unsuccessful runs.

## Preparation and source review

- The first Git whitespace check found a surplus trailing blank line in five
  newly copied assurance scripts. Those blank lines were removed; executable
  behavior was unchanged. The next check passed.
- A commit attempt found no configured Git author in the new clone. The
  plan checkpoint used a per-command automation identity,
  `NDEA-Evolve Experiment 004 <ndea-evolve@localhost>`, consistent with the
  predecessor's experiment-specific automation convention. No global Git
  configuration or user identity was changed.
- Independent source review caught a sign in a control's explanatory comment:
  multiplying the physical-time quadratic coefficient by minus two yields
  `A²+B²+2AB`. The comment was corrected; the control's algebraic statement
  did not change.
- The initial controls draft lacked the promised finite-step exponential
  inequality witness. A focused A=0, B=I, t=π scalar matrix witness and a
  matrix-to-production-CLM bridge were added before compilation.
- The derivation was aligned with the implemented four-comparison route:
  `62+100+2+18=182`, rather than the possible direct exponential-remainder
  route's `164`. Both imply the unchanged frozen constant 1000; only the
  implemented route is claimed in the production proof.

## Local proof attempt 1

Run `20260908T000523.547008Z_2` failed after approximately 139 seconds.
The exact quadratic cancellation, grouped polynomial tail estimate, and
three-factor replacement arguments elaborated, but the full endpoint did
not qualify. Diagnostics identified an underspecified intermediate inequality
in the polynomial norm bound and broad `norm_num` simplification that
expanded the sum-generator operator in goals but not in matching hypotheses.
The endpoint also exhausted the default 200,000-heartbeat budget after those
failures. The repair uses explicit intermediate inequalities and targeted
denominator normalization. The frozen mathematical statement is unchanged.

## Local proof attempt 2

Run `20260908T000842.464989Z_2` failed after approximately 154 seconds with
one remaining intermediate-inequality elaboration error in the polynomial
norm bound. The broad-simplification and heartbeat failures from attempt 1
did not recur. The repair makes both summands of that inequality explicit
with `add_le_add`; no theorem statement, constant, or hypothesis changes.

## Local proof acceptance

Attempt 3, `20260908T001154.280926Z_2`, passed in 203.744479 seconds with no
warnings or errors. Its endpoint axiom row contains only the three allowed
standard axioms. No heartbeat-limit increase or proof-policy relaxation was
needed. The earlier failed logs, including any provisional axiom diagnostics
from incomplete elaboration, are retained but cannot qualify the release.

## Controls attempt 1

Run `20260908T001908.496129Z_2` failed after approximately 179 seconds.
The finite-step exponential witness needed an explicit `: Mat 1` annotation
on its product before applying the two entry indices. The other twenty
public control declarations checked with only standard axioms. Adding the
type annotation does not change the intended matrix statement or its scope;
the complete controls source is rechecked afterward.

## Controls acceptance

Run `20260908T002238.924155Z_2` passed in 112.081212 seconds. All twenty-one
public control declarations have only the accepted standard axiom dependencies.
Unused-simp and unnecessary sequence-focus linter warnings and an informational
ring suggestion are retained verbatim. They are not Lean errors, and no linter
was disabled to suppress them. The new logs directory's `.gitattributes`
disables Git whitespace checks only for raw `.log` files so exact diagnostics
are preserved; production, control, and script whitespace checks remain active.
