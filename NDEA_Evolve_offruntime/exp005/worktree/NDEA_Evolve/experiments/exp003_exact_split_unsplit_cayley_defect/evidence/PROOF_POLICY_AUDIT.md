# Proof-policy and log audit

The Step 3 production theorem and control file were scanned for word-boundary
occurrences of `sorry`, `admit`, `native_decide`, and `unsafe`. The grep exit
code was 1 (no matches). The Julia/Python/assurance sources were scanned the
same way with no matches. A separate anchored scan for custom `axiom` or
`axioms` declarations returned exit code 1 (no matches).

The qualifying modular run reports the public Step 2 theorem, both public
Step 3 theorems, and all three Step 3 control conclusions as depending only on
`[propext, Classical.choice, Quot.sound]`. The independent combined run reports
the same list for the Step 3 controls.

A scan of the passing Lean, Julia, and Python logs for `error:` or `sorryAx`
returned exit code 1 (no matches). Every qualifying command receipt records
exit code 0. Lean messages about sequence focus, unreachable trailing tactics,
and intermediate `ring` suggestions are warnings in runs that proceed to the
final signatures and axiom reports.

The separately named combined attempts 1 and 2 are excluded from passing
evidence. They record rejected control arithmetic normalization attempts and
were superseded by passing attempt 3.
