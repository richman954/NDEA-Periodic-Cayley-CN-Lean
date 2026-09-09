"""Write the review report only after all fresh-VM evidence is accepted."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
read=lambda p:json.loads((root/p).read_text())
transfer=read('FINAL_TRANSFER_CHECK.json');cross=read('CROSS_ENVIRONMENT_COMPARISON.json')
if transfer.get('passed') is not True or cross.get('passed') is not True:
    raise RuntimeError('Fresh verification/transfer has not passed')
remote=root/'downloaded_evidence/recheck_evidence'
final=json.loads((remote/'final_verification/RESULT.json').read_text())
suite=json.loads((remote/'historical_verification/RESULT.json').read_text())
numeric=json.loads((remote/'final_verification/evidence/numerical_checks.json').read_text())
if not final['passed'] or not suite['passed'] or not numeric['passed']:
    raise RuntimeError('A required check is incomplete')
allocation=read('VM_ALLOCATION.json');export=read('EXPORT_RECEIPT.json')
inventory=read('ALL_PUBLIC_THEOREMS.json');history=read('historical_inputs/HISTORICAL_INPUTS.json')
counts={key:inventory['per_experiment_public_counts'][key]+history['positive_audit_counts_by_experiment'].get(key,0)
        for key in inventory['per_experiment_public_counts']}
rows='\n'.join(f'| {key.replace("Exp", "")} | {value} |' for key,value in counts.items())
checks='\n'.join(f'| {row["name"]} | {"Passed" if row["expectation"]=="pass" else "Expected rejection confirmed"} | '
                 f'{row["elapsed_seconds"]:.3f} | [log](downloaded_evidence/recheck_evidence/historical_verification/{row["name"]}.log) |'
                 for row in suite['checks'])
text=f'''# Experiments 001–008 — additional fresh Colab VM verification

Completed September 8, 2026. **The additional VM check passed: 473 distinct
public theorem/control audits, four original anonymous positive examples, and
13 deliberately false claims rejected at their expected proof locations.**
The exact sealed Experiment 008 check also passed all 90 audits independently.
Those 90 are included in the 473 distinct count, not added to it.

The user requested another machine to double-check the completed work. The
new CPU runtime was `{allocation['session']}`, VM `{allocation['vm_id']}`,
distinct from `{allocation['previous_vm_id']}`. The initial runtime check
found no prior project directories. It downloaded its own pinned Lean 4.31.0
distribution, all nine dependency source revisions, and compatible library
cache. No local project build artifacts were uploaded.

## What the new machine checked

The exact sealed Experiment 008 source and verifier were rerun unchanged. The
compiler finished in **{final['elapsed_seconds']:.3f} seconds**, and its result
was accepted at `{final['end_utc']}`. All 90 audit results agree with both the
original local run and the first independent Colab run. All **9,868 external
artifact hashes** agree across these three environments and remained unchanged
during each exact-source check.

The complete retained source contains 332 public declarations across
Experiments 002–008. An additional source file has the sealed source as its
exact prefix and adds only 242 axiom-print commands. Separate historical
checks restore Experiment 001 and older standalone controls omitted from that
retained source. Their mathematical statements and proof bodies are preserved;
external imports are collected at the beginning and old audit commands are
replaced with the complete fresh catalog. Existing import-only compatibility
copies are explicitly recorded in the provenance inventory.

| Experiment | Distinct public audits |
|---|---:|
{rows}
| **Total** | **473** |

These counts include supporting lemmas and control witnesses; they are not
counts of independent mathematical endpoints. The four anonymous Experiment
001 positive examples are checked through successful elaboration. The six
negative drivers cover 13 deliberately false claims: four scalar claims,
seven operator claims, and two contraction claims. Each produced ordinary
Lean exit 1 with the exact expected error lines, counts, and mathematical
diagnostic fragments. Import failures, unknown identifiers, resource failures,
and unrelated errors would not satisfy the rejection criteria.

| Supplemental source check | Accepted outcome | Compiler seconds | Evidence |
|---|---|---:|---|
{checks}

The supplementary checks used **{suite['dependency_artifacts']:,}** isolated
external artifacts because the original Experiment 001 source imports the full
`Mathlib` module. That larger library contains the same 9,868 artifacts used
by the exact Experiment 008 check. Both verification import paths exclude
project build artifacts. Every positive audit uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Numerical diagnostics and preservation

The unchanged Experiment 008 numerical script was also rerun on the new VM.
All **{len(numeric['stage_checks'])} stage cases** and
**{len(numeric['global_checks'])} global-error cases** passed, including
Parseval, wrapped-grid intertwining, aliasing, and arbitrary-initialization
checks. The finest observed orders were
**{numeric['joint_refinement'][-1]['observed_order']:.6f}** jointly,
**{numeric['temporal_refinement'][-1]['observed_order']:.6f}** temporally, and
**{numeric['lie_refinement'][-1]['observed_order']:.6f}** for the unsymmetric Lie
control. These are supporting floating-point diagnostics, separate from proofs.

The original Experiment 008 review packet and all 254 sealed payload files
were checked unchanged. The earlier frozen predecessor manifests still match
all 889/21/99/217 entries. New evidence is saved in this separate recheck
folder and archive. No mathematical theorem was changed or extended.

## Evidence and scope

- [Validated transfer](FINAL_TRANSFER_CHECK.json): all
  **{transfer['evidence_files_checked']}** exported file hashes, all uploaded
  sources/tools, compiler logs, positive audits, and exact rejection diagnostics.
- [Cross-environment comparison](CROSS_ENVIRONMENT_COMPARISON.json).
- [Fresh VM allocation](VM_ALLOCATION.json) and [initial state](FRESH_VM.json).
- [Exact sealed-source result](downloaded_evidence/recheck_evidence/final_verification/RESULT.json).
- [Historical suite result](downloaded_evidence/recheck_evidence/historical_verification/RESULT.json).
- [Numerical result](downloaded_evidence/recheck_evidence/final_verification/NUMERICAL_RESULT.json).
- [Retained declaration inventory](ALL_PUBLIC_THEOREMS.json),
  [historical provenance](historical_inputs/ORIGINAL_SOURCE_INVENTORY.json),
  and [scope explanation](HISTORICAL_CHECK_PLAN.md).
- [Reproduction instructions](REPRODUCE.md) and [saved-file guide](SAVED_FILES.md).

The final qualification and package checks are recorded separately in
`FINAL_VERIFICATION.json` and the external `FINAL_PACKET_RECEIPT.json`.
The complete review ZIP is `Experiments_001-008_Fresh_VM_Recheck_20260908.zip`
in `/home/richman954/`, with a neighboring checksum file.

The compiler, core libraries, and compatible compiled external libraries remain
trusted inputs. This work does not rebuild Lean/Mathlib or prove
source-to-artifact correspondence. It checks the accepted Lean proof and
control chain through Experiment 008 plus its latest numerical diagnostics;
it does not rerun every historical Python/Julia assurance test, figure build,
or archive-restoration exercise. Experiment 008's mathematical scope remains
a fixed finite Fourier band with constant noncommuting internal matrices.

Sealed combined source SHA-256:
`{inventory['combined_sha256']}`.

Fresh independent evidence archive: `{Path(export['archive']).name}`.
SHA-256: `{export['archive_sha256']}`.
'''
with (root/'REPORT.md').open('x') as out:out.write(text)
print(json.dumps({'report':str(root/'REPORT.md'),'unique_audits':sum(counts.values()),
                  'expected_rejections':transfer['false_claims_rejected']}))
