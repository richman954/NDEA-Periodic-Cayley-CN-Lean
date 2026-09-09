# Proof-policy and log audit

The Step 4 production, controls, assurance scripts, and retained probe sources
were scanned for word-boundary occurrences of `sorry`, `admit`,
`native_decide`, and `unsafe`. The grep exit code was 1 (no matches). A
separate anchored scan for custom `axiom`, `constant`, or `opaque` declarations also
returned exit code 1 (no matches).

The qualifying combined and modular runs report the four audited principal
Step 4 declarations and all three Step 4 control conclusions as depending only on
`[propext, Classical.choice, Quot.sound]`. A scan of both passing logs for
`error:` or `sorryAx` returned exit code 1 (no matches). Both qualifying
receipts record exit code 0.

Non-failing linter messages inherited from predecessor proof syntax do not
affect the final signatures or axiom reports. The four earlier combined logs
are explicitly named and excluded as rejected developmental evidence; some
contain `sorryAx` only because Lean replaces declarations containing failed
goals during continued diagnostic elaboration.
