# Experiment 011 verification infrastructure adaptation

The verification workflow was adapted only into Experiment 011 from the sealed
Experiment 010 scripts. No predecessor source, receipt, or archive was edited.
The foundation is the exact accepted Experiment 010 combined source, SHA-256
`fb7b27b42d0baaca9ab8b30f9ba80bb0a5b8999986342fe8538e880bb3947ef0`.

The current intended module order is `SolutionLipschitz`, `Reconstruction`,
`ScheduleBounds`, `UniformConvergence`, and `Controls`. Final reconstruction
must use the confirmed dependency order. The generator derives the complete
new public theorem catalog and external imports from the actual source files;
it checks the frozen foundation and rejects unknown project imports.

Final local and independent checks reconstruct the same combined source and
catalog, use an isolated external-library closure, and verify the complete
axiom log. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Compiler and compatible external library artifacts remain trusted
inputs; the procedure does not rebuild Lean or Mathlib from source.

The new remote paths are under `/content/exp011_check`, on the intended session
`exp011-independent-check`. The receiver pins the accepted Experiment 010
environment receipt and requires a distinct boot identity. The recorded prior
VM list must include Experiment 010, Experiment 009, and both retained
Experiment 008 VM identities. A copied receipt cannot turn the old runtime
into a fresh Experiment 011 allocation.

Bootstrap preparation binds the actual final combined source to the dependency
request. It fills the launcher's archive and bootstrap-script pins only after
source freeze. Final source preparation independently reconstructs the inputs
before packaging. Both preparations reject repeated deliveries without
modifying their previous fixture outputs.

The receiver verifies bootstrap inputs and scripts, all completed command-log
hashes and command vectors, final source hashes, local and independent compiler
audits, and equal external artifact manifests. Its accepted file maps bind the
evidence bytes for final qualification.

All 16 bounded offline checks passed in
[`evidence/INFRASTRUCTURE_TESTS.json`](evidence/INFRASTRUCTURE_TESTS.json).
The schema fixture is explicitly adapted from accepted Experiment 010 evidence;
it is not an Experiment 011 Lean proof run or a new VM verification. The tests
cover catalog reconstruction, immutable foundation rejection, delivery
roundtrips and preservation, bootstrap acceptance, failed commands, incomplete
cache roots, damaged or missing logs, and a reused predecessor VM identity.

The read-only predecessor check also passed. It preserves the seven inherited
manifest inventories and adds all 169 sealed Experiment 010 payload hashes.
The four retained review archives, including the Experiment 010 ZIP, match
their pinned checksums. See
[`evidence/PREDECESSOR_PRESERVATION.json`](evidence/PREDECESSOR_PRESERVATION.json).

No network operation or new proof compilation was performed as part of this
infrastructure adaptation. Accepted Experiment 011 proof and VM results must
be recorded by the actual later checks.
