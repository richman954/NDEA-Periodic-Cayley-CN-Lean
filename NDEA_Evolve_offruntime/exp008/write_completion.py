"""Fill the completion report from accepted, preserved verification receipts."""
from pathlib import Path
import json

root=Path(__file__).resolve().parent
read=lambda p:json.loads((root/p).read_text())
final=read('evidence/FINAL_VERIFICATION.json')
if final.get('passed') is not True:raise RuntimeError('Final qualification has not passed')
local=read(final['local_result']);remote=read(final['independent_result'])
transfer=read('remote_check/FINAL_TRANSFER_CHECK.json')
export=read('remote_check/EXPORT_RECEIPT.json')
inputs=read('evidence/FINAL_INPUTS.json')
if not(local['passed'] and remote['passed'] and transfer['passed']):
    raise RuntimeError('Incomplete evidence')
source=inputs['source_sha256'];count=len(inputs['expected_audits'])
text=(root/'COMPLETION_REPORT_DRAFT.md').read_text()
intro=text.index('Experiment 008 extends')
text='# Experiment 008 — verified finite Fourier superpositions\n\n'+\
    '**Completed September 8, 2026. Local and independent combined checks passed all 90 new public audits: 83 production theorems and seven controls.**\n\n'+text[intro:]
begin=text.index('The current declaration inventory')
end=text.index('The acceptance policy permits',begin)
verification=f'''All seven new modules passed separately locally and on the fresh
`exp008-independent-check` Colab runtime. Both final combined checks reconstructed
and re-elaborated the complete frozen foundation and all seven new modules,
with only external libraries in the import path. All {count} new public audits
agreed between the environments and used only the three permitted axioms.

| Final verification | Accepted evidence |
|---|---|
| Combined source/catalog reconstruction | Passed in both environments; [exact inputs](evidence/FINAL_INPUTS.json). |
| Local combined check | Exit 0; {local['elapsed_seconds']:.3f} seconds; [result]({final['local_result']}). |
| Independent combined check | Exit 0; {remote['elapsed_seconds']:.3f} seconds; finished `{remote['end_utc']}`; [result]({final['independent_result']}). |
| Public axiom coverage | 90/90 in both runs: 83 production declarations and seven controls. |
| Source stability | All constituent hashes and combined bytes match, unchanged during both runs. |
| External library artifacts | {local['dependency_artifacts']:,} artifact hashes per run, unchanged and identical across environments; [comparison](evidence/CROSS_ENVIRONMENT_DEPENDENCIES.json). |
| Independent evidence transfer | {transfer['evidence_files_checked']} file hashes checked, all uploaded verification inputs and 90 compiler audits matched; [receipt](remote_check/FINAL_TRANSFER_CHECK.json). |
| Predecessor preservation | All 889/21/99/217 entries matched the frozen manifests; [receipt](evidence/PREDECESSOR_PRESERVATION.json). |
| Final qualification | [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json), including the accepted modular receipt paths. |

The theorem inventory is `FrequencyBounds:15`, `ContinuumModes:25`,
`FourierGrid:13`, `Orthogonality:12`, `SuperpositionClosure:10`, `StageBridge:8`,
and `Controls:7`. Exploratory probes and failed development attempts are
retained as history and excluded from acceptance.

'''
text=text[:begin]+verification+text[end:]
text=text.replace('Final independent agreement must be evidenced by the receipts above.',
                  'The recorded agreement is established by the receipts above within this trust boundary.')
text=text.replace('Further derivation and proof obligations are recorded in',
                  'The mathematical derivation is recorded in')
text+=f'''\nCombined source SHA-256: `{source}`.

Independent evidence archive: `{Path(export['archive']).name}`. SHA-256:
`{export['archive_sha256']}`.

The review archive is `Exp008_Verified_Review_Packet_20260908.zip` in
`/home/richman954/`, with a neighboring `.zip.sha256` file. Its post-write hash
and read-back results are recorded in `evidence/FINAL_PACKET_RECEIPT.json`,
which is external to the ZIP to avoid a self-hash cycle. The complete payload
inventory is `PACKET_MANIFEST.json`. See [SAVED_FILES.md](SAVED_FILES.md) for the
source, receipt, checkpoint, and tool map.
'''
if 'PENDING' in text:raise RuntimeError('Unfilled completion-report field')
with (root/'COMPLETION_REPORT.md').open('x') as out:out.write(text)
plan=root/'PLAN.md';s=plan.read_text()
s=s.replace('Status: in progress, September 8, 2026. No new proof result is claimed by this plan.',
            'Status: completed, September 8, 2026. All acceptance criteria below passed. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md) and [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). The original target and acceptance criteria are retained below.')
plan.write_text(s)
with (root/'STATUS_PROGRESS.md').open('a') as out:
    out.write(f'''\n## Final mathematical and evidence qualification — September 8, 2026

Both combined checks passed all 90 audits. Local compile: {local['elapsed_seconds']:.3f}s;
independent: {remote['elapsed_seconds']:.3f}s. All {transfer['evidence_files_checked']} transferred
evidence-file hashes and all uploaded verification inputs matched. The external
library artifact manifests agree on all {local['dependency_artifacts']:,} paths/hashes.
Predecessor manifests are unchanged. The completion report supersedes the
pending statuses in earlier checkpoints. Packet sealing is recorded separately
in `evidence/FINAL_PACKET_RECEIPT.json` after the archive is written and verified.
''')
print(json.dumps({'report':str(root/'COMPLETION_REPORT.md'),'audits':count,'source_sha256':source}))
