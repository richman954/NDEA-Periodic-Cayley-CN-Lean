# Experiment 012 verification infrastructure adaptation

The verification workflow was adapted into Experiment 012 from the sealed
Experiment 011 scripts. No predecessor source, receipt, or archive was edited.
The foundation is the exact accepted Experiment 011 combined source:
`6e516d1a5cbd1eae23feddcb9b26a29c12a15a6a0d45928c891acd9be453e3e5`.

## Inputs and interfaces

The current module order is `EnergyLocal`, `EnergyConservation`,
`EnergySeparation`, `ClassicalUniqueness`, and `Controls`. The generator derives
the complete public theorem catalog and external imports from these actual
sources. It rejects a changed foundation or unknown project import. Existing
classical-solution and reconstruction modules are embedded in the foundation.

`make_combined.py` writes `lean/Exp012Combined.lean` and
`evidence/FINAL_INPUTS.json`. After passing sources are frozen,
`prepare_final_sources.py` and `prepare_bootstrap_inputs.py` create their
respective exact source deliveries. Until then, bootstrap launcher pins remain
`UNPREPARED`. No real delivery bundle was made during this adaptation.

`verify_combined.py` retains the same explicit root, compiler, package, and
output arguments as Experiment 011. It reconstructs the exact source/catalog,
isolates the required external artifact closure, excludes project artifacts,
and checks all public axiom declarations. The permitted axiom set remains
`propext`, `Classical.choice`, and `Quot.sound`. The compiler and compatible
external artifacts remain trusted inputs.

## New predecessor and environment pins

| Preserved item | Pin |
|---|---|
| Experiment 011 manifest, 179 entries | `789e6a4154c82c6963572fed0a550666bed4e7d9ebbe41387ad379a133aabc19` |
| Experiment 011 review ZIP | `f6f52467bbed628201cc02f740a6203cb1b0ad57b3b257a8a89a1779e223cac3` |
| Experiment 011 environment receipt | `915f9cd8cfa7e048cef587b053bafe84f8d389addcfb4cf0ab83f504fcd5035b` |

The new session is `exp012-independent-check`, rooted at
`/content/exp012_check`. The receiver requires a boot distinct from Experiment
011's `3ee83a63-6560-4416-ac97-a34975a3e03e`. Its VM history must include
`m-s-kkb-usw3b1-3oqo9i5fec2ow` and the retained Experiment 010, 009, and two
Experiment 008 allocations; the new VM must differ from all of them.

Compiler, Mathlib, dependency-lock, import-walker, and axiom-parser pins are
unchanged. Bootstrap binds the actual final combined source to its library
request, so any new interval-integral imports are included automatically.
The receiver checks exact deliveries, completed bootstrap command vectors and
log hashes, final sources and audit logs, and equal library artifact manifests.
Accepted file maps bind the evidence bytes for final qualification.

## Adaptation checks

All 16 focused offline tests passed; see
[`evidence/INFRASTRUCTURE_TESTS.json`](evidence/INFRASTRUCTURE_TESTS.json).
They exercise source/catalog reconstruction, foundation rejection, delivery
roundtrips and repeat preservation, bootstrap schema acceptance, failed or
incomplete commands, damaged/missing logs, and reused VM identity rejection.
The transformed Experiment 011 bootstrap evidence is explicitly a synthetic
protocol fixture, not a new Experiment 012 proof or VM check.

The read-only predecessor check passed all nine retained manifest inventories
and five review archives, adding all 179 Experiment 011 payload hashes; see
[`evidence/PREDECESSOR_PRESERVATION.json`](evidence/PREDECESSOR_PRESERVATION.json).

New files comprise the six top-level infrastructure scripts (including the
offline test), seven `remote_check` scripts, two `verification_tools` helpers,
four pinned bootstrap helper/lock inputs, the copied predecessor environment
receipt, this note, and the two check receipts. No network operation or proof
compilation was performed by this infrastructure adaptation.
