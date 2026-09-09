# Proof-policy and log audit

The production theorem, control file, and three shadow sources were scanned for
word-boundary occurrences of `sorry`, `admit`, `native_decide`, and `unsafe`.
The grep exit code was 1 (no matches). A separate anchored scan for custom
`axiom` or `axioms` declarations also returned exit code 1 (no matches).

Intentional `#print axioms` audit commands are not declarations. The modular
run reports:

- all three Step 1 public theorems;
- the Step 2 public norm theorem;
- both packaged negative controls;

as depending only on `[propext, Classical.choice, Quot.sound]`. The independent
combined-control run reports the same list for both packaged controls.

A scan of both passing logs for `error:` or `sorryAx` returned exit code 1 (no
matches). Both command receipts record exit code 0. The linter messages about
sequence focus and intermediate `ring` tactic suggestions are warnings, not
errors, and occur in runs that proceed to the final checks and axiom reports.

The separately named failed-cleanup log is excluded from passing evidence. It
records the rejected attempt in which necessary intermediate `ring` calls had
temporarily been removed.
