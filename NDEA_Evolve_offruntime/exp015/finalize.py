"""Qualify completed checks and seal a checksum-verified Experiment 015 packet."""
import datetime, hashlib, importlib.util, json, os, subprocess, sys, zipfile
from pathlib import Path

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def write_json(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
stamp=datetime.datetime.now(datetime.timezone.utc)
archive=Path('/home/richman954')/f'Exp015_Verified_Review_Packet_{stamp:%Y%m%d}.zip'
require(not archive.exists() and not (root/'PACKET_MANIFEST.json').exists(),
    'Packet or sealed manifest already exists; preserve it before any writes')
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
transfer=json.loads((root/'remote_check/FINAL_TRANSFER_CHECK.json').read_text())
local=json.loads((root/'evidence/local_combined/RESULT.json').read_text())
remote_root=root/'remote_check/downloaded_evidence'
remote=json.loads((remote_root/'final_verification/RESULT.json').read_text())
for name,result in [('transfer',transfer),('local',local),('independent',remote)]:
    require(result.get('passed') is True,'Unaccepted '+name+' check')
require(bool(transfer['accepted_local_files']) and bool(transfer['accepted_independent_files']),
    'Receiving checker did not bind accepted evidence bytes')
require(sha(root/'remote_check/check_download.py')==transfer['checker_sha256'],
    'Receiving checker changed after acceptance')
export=json.loads((root/'remote_check/EXPORT_RECEIPT.json').read_text())
evidence_archive=root/'remote_check'/Path(export['archive']).name
require(export.get('passed') is True and sha(evidence_archive)==export['sha256']==
    transfer['archive_sha256'] and evidence_archive.stat().st_size==export['bytes'] and
    export['payload_files']==transfer['verified_payload_files'],'Export receipt/archive mismatch')
require(transfer['bootstrap_verification'].get('passed') is True,'Fresh bootstrap was not accepted')
for name,digest in transfer['accepted_local_files'].items():
    require(sha(root/name)==digest,'Locally accepted evidence changed: '+name)
for name,digest in transfer['accepted_independent_files'].items():
    require(sha(remote_root/name)==digest,'Independent accepted evidence changed: '+name)
require(transfer['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp015Combined.lean'),
    'Final source changed')
spec=importlib.util.spec_from_file_location('generator',root/'make_combined.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
combined,reconstructed=gen.build(root)
require(combined==(root/'lean/Exp015Combined.lean').read_text() and reconstructed==inputs,
    'Final source/catalog reconstruction changed')
review=json.loads((root/'evidence/REVIEW_CHECK.json').read_text())
require(review.get('passed') is True and review['current_source_hashes']==inputs['source_hashes']
    and review['public_catalog_total']==len(inputs['expected_audits']),
    'Review does not cover the current proof/catalog')
require(sha(root/'REVIEW.md')==review['review_sha256'] and
    all(sha(root/name)==digest for name,digest in review['reviewed_tool_hashes'].items()),
    'Reviewed review/tool bytes changed')
require('finalize.py' in review['reviewed_tool_hashes'], 'Finalizer itself was not reviewed')
reviewed_documents=review.get('reviewed_document_hashes')
require(isinstance(reviewed_documents,dict) and
    {'MATHEMATICAL_DERIVATION.md','REPRODUCE.md','SAVED_FILES.md','INFRASTRUCTURE_REVIEW.md'} <=
    set(reviewed_documents) and
    all(sha(root/name)==digest for name,digest in reviewed_documents.items()),
    'Reviewed document coverage or bytes changed')
modules={}
for name,digest in inputs['source_hashes'].items():
    require(sha(root/name)==digest,'Source changed: '+name)
    if not name.startswith('lean/') or name.endswith('Exp014Foundation.lean'):continue
    accepted=[]
    for p in sorted((root/'evidence').glob('*_'+Path(name).stem+'.json')):
        d=json.loads(p.read_text())
        if d.get('exit_code')==0 and d.get('sources_unchanged') is True and \
            d.get('source_sha256_before')==d.get('source_sha256_after')==digest:
            require(sha(Path(d['log']))==d['log_sha256'],'Modular log changed')
            require(bool(d['output_sha256']) and all(Path(k).is_file() and sha(Path(k))==v
                for k,v in d['output_sha256'].items()),'Modular output changed')
            accepted.append(str(p.relative_to(root)))
    require(bool(accepted),'No accepted modular check for '+name)
    modules[name]=accepted[-1]
subprocess.run([sys.executable,'-B',str(root/'check_predecessors.py')],check=True)
baseline=json.loads((root/'evidence/BASELINE.json').read_text())
archives=[(Path('/home/richman954/Exp014_Verified_Review_Packet_20260909.zip'),
    baseline['exp014_packet_sha256'])]
for p,digest in archives:require(sha(p)==digest,'Earlier archive changed: '+p.name)
record={'passed':True,'utc':stamp.isoformat(),'source_sha256':inputs['source_sha256'],
    'source_hashes':inputs['source_hashes'],'expected_audits':inputs['expected_audits'],
    'audits':len(inputs['expected_audits']),'accepted_modular_receipts':modules,
    'local_result_sha256':sha(root/'evidence/local_combined/RESULT.json'),
    'independent_result_sha256':sha(remote_root/'final_verification/RESULT.json'),
    'transfer_receipt_sha256':sha(root/'remote_check/FINAL_TRANSFER_CHECK.json'),
    'independent_archive_sha256':transfer['archive_sha256'],
    'bootstrap_verification':transfer['bootstrap_verification'],
    'review_receipt_sha256':sha(root/'evidence/REVIEW_CHECK.json'),
    'predecessor_receipt_sha256':sha(root/'evidence/PREDECESSOR_PRESERVATION.json'),
    'qualification':'Quantitative spatial L2 forcing and actual-residual stability, with coefficient one and retained initial error, for classical periodic complex Hilbert-valued Schrödinger fields with positive period, a common pointwise selfadjoint potential and the stated continuity assumptions. Applies to the Exp014 regular static variable-potential solution. No convergence theorem for discrete iterates or reconstructions is claimed. Compatible compiler/library artifacts remain trusted inputs.'}
write_json(root/'evidence/FINAL_VERIFICATION.json',record)
report=f'''# Experiment 015 — quantitative forcing and residual stability

Completed {stamp.date().isoformat()}. All **{record['audits']} new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM.
All {len(modules)} new modules passed separately. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in the audited axiom dependencies.

For positive spatial period L and any origin b, define the spatial L2 norm as
the square root of the integral of the squared Hilbert norm over [b,b+L]. Classical periodic
Schrödinger fields u and v with a common pointwise selfadjoint potential and
jointly continuous forcing difference satisfy, for s <= t,

```text
||u(t)-v(t)||L2 <= ||u(s)-v(s)||L2 + integral_s^t ||f(r)-g(r)||L2 dr.
```

The estimate keeps the full initial error and has coefficient one in front
of the forcing integral. The proof derives the squared-error derivative from
Exp013's exact energy identity and uses positive square-root regularization
to include vanishing error. Spatial integral and continuity prerequisites
are proved under the stated hypotheses.

A regular approximate field is assigned its actual PDE residual
`i*u_t + u_xx - V*u`. Applying the same estimate turns residual size and
initialization error into an L2 error bound, with joint continuity of the
residual-minus-forcing difference required explicitly. A jointly continuous
operator potential supplies residual continuity from field regularity.
The variable-potential bridge
specializes this result to the unique global regular solution constructed in
Exp014. The exact theorem statements specify all field, period, potential
and forcing regularity assumptions; see the [derivation](MATHEMATICAL_DERIVATION.md)
and [controls](lean/Controls.lean).

| Accepted check | Result |
|---|---|
| New modular sources | {len(modules)} passed |
| Local combined source | {record['audits']} audits; exit 0; {local['elapsed_seconds']:.3f} seconds |
| Independent combined source | {record['audits']} audits; exit 0; {remote['elapsed_seconds']:.3f} seconds |
| Source/catalog | Exactly reconstructed; unchanged during both checks |
| External artifact hashes | {transfer['dependency_artifacts_agree']:,} agree across environments |
| Evidence transfer | {transfer['verified_payload_files']} payload hashes and all compiler audits verified |
| Predecessors | Sealed predecessor manifests and Exp014 packet preserved |

The separate CPU session is `exp015-independent-check`, initially empty at
`/content/exp015_check`. The pinned compiler and compatible external libraries
were independently downloaded. Both combined checks exclude project artifacts
from their import paths. They re-elaborate the exact sealed Exp014 combined
proof bodies, including its generic Exp013 foundation, alongside the new source.
Only the 143 prior axiom-print commands are removed from that foundation; the
new audit catalog covers Exp015 declarations only. Earlier numerical proof
chains remain preserved in their accepted packets. Lean 4.31.0 and compatible
compiled library artifacts are trusted inputs and were not rebuilt from source.

This is a continuous PDE stability and residual-to-error milestone. Convergence
of actual discrete iterates or reconstructed numerical fields, discrete
consistency bounds, refinement schedules and numerical convergence rates for
the enlarged variable-potential class require additional work.

Read [review](REVIEW.md), [reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).
Combined SHA-256: `{inputs['source_sha256']}`.
'''
(root/'COMPLETION_REPORT.md').write_text(report)
plan=(root/'PLAN.md').read_text().replace('Status: implementation in progress; no completed error estimate claimed.','Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).')
(root/'PLAN.md').write_text(plan)
excluded={'PACKET_MANIFEST.json','evidence/FINAL_PACKET_RECEIPT.json'}
payload={}
for cur,dirs,names in os.walk(root):
    dirs[:]=[d for d in dirs if d not in {'build','dependencies','isolated_dependencies','__pycache__','.git'}]
    for name in names:
        p=Path(cur)/name;rel=str(p.relative_to(root))
        if p.is_file() and not p.is_symlink() and rel not in excluded:payload[rel]=p.read_bytes()
manifest={n:hashlib.sha256(data).hexdigest() for n,data in sorted(payload.items())}
write_json(root/'PACKET_MANIFEST.json',manifest)
payload['PACKET_MANIFEST.json']=(root/'PACKET_MANIFEST.json').read_bytes()
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name,data in sorted(payload.items()):z.writestr('exp015/'+name,data)
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'ZIP CRC failure')
    require(len(z.namelist())==len(set(z.namelist()))==len(payload),'ZIP coverage mismatch')
    for name,data in payload.items():require(z.read('exp015/'+name)==data,'ZIP readback mismatch')
for name,digest in manifest.items():require(sha(root/name)==digest,'Source changed during packaging')
require((root/'PACKET_MANIFEST.json').read_bytes()==payload['PACKET_MANIFEST.json'],
    'Manifest changed during packaging')
for p,digest in archives:require(sha(p)==digest,'Earlier archive changed during packaging')
receipt={'passed':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,
    'manifest_entries':len(manifest),'verified_zip_files':len(payload),
    'manifest_sha256':sha(root/'PACKET_MANIFEST.json'),
    'qualification':'Every ZIP member read back byte-for-byte; CRC and payload manifest hashes passed. This receipt and the neighboring checksum file are outside the ZIP to avoid a self-hash cycle.'}
write_json(root/'evidence/FINAL_PACKET_RECEIPT.json',receipt)
Path(str(archive)+'.sha256').write_text(receipt['archive_sha256']+'  '+archive.name+'\n')
print(json.dumps(receipt))
