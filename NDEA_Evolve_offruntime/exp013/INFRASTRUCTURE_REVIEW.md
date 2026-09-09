# Experiment 013 verification infrastructure adaptation

The verification workflow was adapted from the sealed Experiment 012 scripts.
No predecessor source, receipt, or archive was edited. The foundation is the
exact accepted Experiment 012 combined source:
`ff98d87926fe6729202d77119d84e3ff3b3a3664ab607c0069a52db2c9f8547d`.

## Inputs and interfaces

The production order is `GenericClassical`, `GenericEnergy`,
`GenericUniqueness`, `LegacyBridge`, and `Controls`. The generator derives the
complete public theorem/lemma catalog from the actual module sources. It
allows a module containing only structures and definitions; no theorem count
is assumed in advance. Comments are excluded from catalog scanning.

The retained `EnergyLocal`, `EnergyConservation`, `EnergySeparation`, and
`ClassicalUniqueness` modules are recognized as embedded predecessor imports,
along with the earlier classical and reconstruction modules. Unknown project
imports, duplicate public theorem names, and changed foundation bytes are
rejected. The generic modules' external imports are collected automatically;
the new inner-product adjoint import is exercised by the offline fixture.

`make_combined.py` writes `lean/Exp013Combined.lean` and
`evidence/FINAL_INPUTS.json`. Once passing sources are frozen,
`prepare_final_sources.py` and `prepare_bootstrap_inputs.py` prepare exact
source deliveries and bind the bootstrap launcher. Its pins remain
`UNPREPARED` until that step. No real delivery bundle or combined proof was
created during this infrastructure adaptation.

`verify_combined.py` retains explicit root, compiler, package, and fresh output
arguments. It reconstructs the source/catalog, copies only the required
external artifact closure, excludes project artifacts from the final import
path, and checks every cataloged axiom declaration. Source and library hashes
are checked again after elaboration. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted in audited theorem dependencies. The compiler and
compatible external library artifacts remain trusted inputs.

## New predecessor and environment pins

| Preserved item | Pin |
|---|---|
| Experiment 012 manifest, 171 entries | `f672a80e505e8959e2c15aed3e4f812e97175cf3202fbf42f993137fc6f835e7` |
| Experiment 012 review ZIP | `2c1347c1261c00f1f63e06b7c500235c48dfb5e9b817f25ffb23ea0edc0d596d` |
| Experiment 012 environment receipt | `4bb371158ed752d8f7f0ff2a0cc101187dbc1c50871e87ae8d86df4504c69954` |

The new session is `exp013-independent-check`, rooted at
`/content/exp013_check`. The receiving validator requires a boot distinct
from Experiment 012's `a7a2db8d-794b-4bfb-8b4c-fbd00b5140ed`. Its VM history
must include Experiment 012's `m-s-kkb-usw4c1-1loxz56gsupls`, Experiment 011,
010, 009, and both retained Experiment 008 allocations. The new allocation
must differ from all of them.

Compiler, Mathlib, dependency lock, import walker, safe bootstrap helper, and
axiom parser pins are unchanged. The receiver binds the fresh allocation and
initial environment, exact source deliveries, completed bootstrap command
vectors and log hashes, final proof sources and audit logs, and equal library
artifact manifests across the two environments. Accepted local and remote
file maps preserve the exact evidence bytes for final qualification.

No network action or Google Drive access was performed by this adaptation.
Remote allocation and proof checks are managed separately from local backups.

## Focused adaptation checks

All 16 offline checks passed; see
[INFRASTRUCTURE_TESTS.json](evidence/INFRASTRUCTURE_TESTS.json). They exercise
catalog/comment handling, the generic adjoint import, unknown project import
and duplicate declaration rejection, foundation pin rejection, both delivery
roundtrips and refusal to modify repeated preparations, bootstrap schema
acceptance, failed or incomplete commands, wrong cache output, missing cache
imports, damaged/missing command logs, and reused VM identity rejection.

The accepted Experiment 012 bootstrap evidence was transformed only inside a
temporary synthetic protocol fixture. Its acceptance is not an Experiment 013
mathematical proof or fresh-VM result. Fixture archives were kept outside the
actual experiment delivery paths and removed with the temporary directory.

The read-only predecessor check passed all ten retained manifest inventories
and six review archives, adding all 171 Experiment 012 payload hashes; see
[PREDECESSOR_PRESERVATION.json](evidence/PREDECESSOR_PRESERVATION.json).

The workflow comprises six top-level infrastructure scripts, seven remote
scripts, two pinned verification helpers, four pinned bootstrap helper/lock
inputs, the copied predecessor environment receipt, this note, and the two
check receipts. The root-owned local Lean runner, baseline, mathematical
sources, finalizer, reports, and remote allocation remain separate work.
