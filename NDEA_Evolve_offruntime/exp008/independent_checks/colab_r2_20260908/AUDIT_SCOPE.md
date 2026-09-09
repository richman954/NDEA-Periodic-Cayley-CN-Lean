# Fresh Colab VM r2 — retained proof-chain audit scope

This inventory identifies what is actually declared in the sealed Experiment 008
combined source. It is preparation for the new VM check, not a claim that the new
check has passed. Accepted execution and transfer receipts must record that result.

The source is
[`exp008/lean/Exp008Combined.lean`](../../lean/Exp008Combined.lean), SHA-256
`5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0`.
It contains 31 retained source modules and **332 public theorem/lemma declarations**
from Experiments 002–008. The existing sealed file prints axioms for the 90 new
Experiment 008 declarations. An appended, separate audit overlay supplies the
remaining **242 public declarations** without altering the sealed source bytes.

## Coverage by experiment

| Experiment | Public declarations retained | Mathematical sources and limitations |
|---|---:|---|
| 001 | 0 | The original scalar Fourier-stability source is absent. A separate historical-source check is required to include Experiment 001. |
| 002 | 37 | `OperatorCayley.lean`: Hermitian denominator invertibility, two-sided unitarity, ordered products, exact Cayley commutator/order defect, and the commutation equivalence. This is the compatibility-preserved shadow source retained by the later chain. Its older standalone negative-control module is absent. |
| 003 | 38 | Seven modules cover resolvent contraction, order-defect norm bound, split/unsplit defect, finite-power telescoping, exponential remainder, continuous comparison, and convergence. `EuclideanResolventContraction.lean` contains ten `AdversarialWitnesses` declarations. Other separately archived control modules are not implied to be present. |
| 004 | 9 | `SymmetricCayleyLocal.lean` and `SymmetricCayleyGlobal.lean`: second-order symmetric matrix splitting and fixed-time convergence. The older standalone control module is absent. |
| 005 | 29 | `MeshWeightedStability.lean`, `SymmetricStageResidual.lean`, and `MeshFamilyConvergence.lean`: the weighted stability and conditional stage-residual bridge. The older standalone control module is absent. |
| 006 | 41 | Periodic grid, scalar mode residual, actual matrix bridge, and all six controls: 35 production declarations and six controls. |
| 007 | 88 | All seven new modules: reduced noncommuting model, full spinor grid, continuum solution, reduced/global closure, actual stage bridge, and controls. There are 81 production declarations and seven controls. |
| 008 | 90 | All seven new modules: frequency bounds, continuum modes, Fourier grid, orthogonality, superposition closure, stage bridge, and controls. There are 83 production declarations and seven controls. |
| **Total** | **332** | Public declarations in the retained combined source, including the controls actually present. |

Private helpers are also elaborated by a complete source compile. The inventory
records **24 private theorem declarations** separately and omits their private
compiler-generated names from the public audit list. Definitions, abbreviations,
instances, and external-library declarations are outside this public theorem/lemma
count. They are not thereby omitted from Lean's elaboration or dependency checking.

## Reproducible inventory and line evidence

[`ALL_PUBLIC_THEOREMS.json`](ALL_PUBLIC_THEOREMS.json) records each public name,
experiment, namespace frames, named sections, original source path and SHA-256,
original declaration line, combined declaration line, and source-marker line. Its
`modules` array lists all 31 constituent source files and their public/private
counts. It also records every retained source marker, all excluded private helpers,
the existing 90 names, and the additional 242 names.

[`build_audit_inventory.py`](build_audit_inventory.py) reads the source without
modifying it. It uses the sealed portable verifier's lexer to blank nested Lean
comments and strings while preserving line locations. It tracks namespaces and
sections independently, excludes explicitly private commands, and fails if any
remaining `theorem` or `lemma` token is not accounted for by a declaration command.
Named namespaces and sections must balance. The 31 anonymous `noncomputable section`
commands are intentionally still open at the end of the inlined source; they add
no namespace component to printed names.

Every source marker was resolved to a currently saved source with the same
SHA-256. Every declaration was independently located in that original source, with
matching name and visibility. The resulting Experiment 008 list exactly matches
the sealed 90-name catalog in `exp008/evidence/FINAL_INPUTS.json`.

This is a checked inventory for this source's actual command forms, not a general
Lean parser. The new VM's successful `#print axioms` output is required to confirm
that every proposed fully qualified name resolves as intended. The complete
expected name set is `expected_complete_audit_names` in the JSON file. The minimal
append-only overlay is [`ADDITIONAL_AXIOM_PRINTS.lean.txt`](ADDITIONAL_AXIOM_PRINTS.lean.txt).

To repeat the inventory locally:

```sh
python3 -B NDEA_Evolve_offruntime/exp008/independent_checks/colab_r2_20260908/build_audit_inventory.py
```

This command rewrites only these new inventory outputs. It does not run Lean or
change the sealed Experiment 008 source, its generator, or earlier evidence.

## Historical releases and interpretation

The retained source chain is not the union of every archived Experiment 001–008
release. In particular, Experiment 001 and several separately archived control
modules are absent, and the retained Experiment 002 operator source and Experiment
003 resolvent source are the pinned shadow versions used by later experiments.
A new combined-source pass cannot by itself claim a fresh rebuild of omitted
historical source versions, old checkpoint archives, their numerical diagnostics,
or their Python assurance systems.

The separate historical-input preparation for this VM run must identify those
additional accepted source files and controls, with its own source pins, check
commands, expected audits, and results. The retained inventory here lets that
preparation distinguish missing sources from sources already present. The final
report should state both scopes and their actual accepted receipts.

The earlier results that motivate this scope are recorded in the
[Experiments 001–007 recap](../../../recap_001_007_20260908/MASTER_RECAP.md),
the [Experiment 007 completion report](../../../exp007/COMPLETION_REPORT.md), and
the [Experiment 008 completion report](../../COMPLETION_REPORT.md).

Both the old and new independent checks operate within the same stated trust
boundary: a pinned Lean compiler and compatible compiled core/external libraries
are trusted inputs. Source revision pins and library artifact hashes do not prove
source-to-artifact correspondence or rebuild Lean and Mathlib. The public axiom
policy accepts only `propext`, `Classical.choice`, and `Quot.sound`.
