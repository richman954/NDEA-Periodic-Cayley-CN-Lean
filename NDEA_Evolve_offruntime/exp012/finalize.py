"""Qualify completed checks and seal a checksum-verified Experiment 012 packet."""
import datetime, hashlib, importlib.util, json, os, subprocess, sys, zipfile
from pathlib import Path

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def write_json(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
stamp=datetime.datetime.now(datetime.timezone.utc)
archive=Path('/home/richman954')/f'Exp012_Verified_Review_Packet_{stamp:%Y%m%d}.zip'
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
require(transfer['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp012Combined.lean'),
    'Final source changed')
spec=importlib.util.spec_from_file_location('generator',root/'make_combined.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
combined,reconstructed=gen.build(root)
require(combined==(root/'lean/Exp012Combined.lean').read_text() and reconstructed==inputs,
    'Final source/catalog reconstruction changed')
review=json.loads((root/'evidence/REVIEW_CHECK.json').read_text())
require(review.get('passed') is True and review['current_source_hashes']==inputs['source_hashes']
    and review['public_catalog_total']==len(inputs['expected_audits']),
    'Review does not cover the current proof/catalog')
require(sha(root/'REVIEW.md')==review['review_sha256'] and
    all(sha(root/name)==digest for name,digest in review['reviewed_tool_hashes'].items()),
    'Reviewed documentation/tool bytes changed')
modules={}
for name,digest in inputs['source_hashes'].items():
    require(sha(root/name)==digest,'Source changed: '+name)
    if name.endswith('Exp011Foundation.lean'):continue
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
archives=[(Path('/home/richman954/Exp011_Verified_Review_Packet_20260908.zip'),
    baseline['exp011_review_archive_sha256'])]
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
    'qualification':'Uniqueness for arbitrary functions in the unchanged classical periodic spinor solution class, using derived energy conservation for all real times. Regular Fourier initial data admit exactly one such solution, and the established numerical reconstruction converges uniformly to it. Compiler and compatible external library artifacts are trusted inputs.'}
write_json(root/'evidence/FINAL_VERIFICATION.json',record)
report=f'''# Experiment 012 — classical periodic uniqueness

Completed {stamp.date().isoformat()}. All **{record['audits']} new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM,
with only `propext`, `Classical.choice`, and `Quot.sound`. All {len(modules)} new
modules passed separately.

Any two functions satisfying the unchanged
`Exp010.IsClassicalPeriodicSolution` predicate for
`iUt=-Uxx+(Z+X)U`, period `2π`, and agreeing at a single real time are equal
for every real time and position. This compares arbitrary classical solutions;
a Fourier representation of the competing solution is not assumed.

The proof derives the local identity

```text
∂t ‖u(t,x)‖² = ∂x J(t,x),
J(t,x) = 2 Re ⟨u(t,x), i ∂x u(t,x)⟩.
```

Hermitian symmetry cancels the potential term. Actual differentiability and
periodicity imply periodicity of the spatial derivative and hence of the
flux. A compact time-space rectangle supplies the local majorant needed to
differentiate the energy integral, without any added global time bound.
Thus, for every real base `b` and all real times `s,t`,

```text
∫[b,b+2π] ‖u(s,x)−v(s,x)‖² dx = ∫[b,b+2π] ‖u(t,x)−v(t,x)‖² dx.
```

Equal data at one time make this energy zero. Continuity and positivity of
the integral then force equality at each spatial point. Allowing arbitrary
interval bases covers all real positions directly, including interval endpoints.

For initial data from Fourier coefficients with
`Σ_m (1+|m|)² ‖a_m‖ < ∞`, there exists exactly one solution in this classical
class. Experiment 011's actual reconstructed numerical fields converge
uniformly to that unique solution on `[0,1] × [0,2π]`, with the same explicit
error bound, exact sampled initialization and refinement schedule.

| Accepted check | Result |
|---|---|
| New modular sources | {len(modules)} passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | {record['audits']} audits; exit 0; {local['elapsed_seconds']:.3f} seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | {record['audits']} audits; exit 0; {remote['elapsed_seconds']:.3f} seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly and unchanged during both checks |
| External library hashes | {transfer['dependency_artifacts_agree']:,} agree across environments |
| Evidence transfer | {transfer['verified_payload_files']} payload hashes verified; uploaded inputs and compiler audits matched |
| Earlier experiments | Sealed predecessor manifests and the Exp011 ZIP preserved |

The independent CPU session is `exp012-independent-check`, initially empty at
`/content/exp012_check`. Its compiler and libraries were downloaded
independently. Project build artifacts were excluded from both final combined
import paths. The retained predecessor proof bodies were re-elaborated.
Lean 4.31.0 and compatible compiled external libraries remain trusted inputs;
Lean and Mathlib themselves were not rebuilt from source.

The [exact controls](lean/Controls.lean) exercise nonzero data, necessity of
matching data, zero-data uniqueness, matching at a shifted time, and the flux
sign. This analytic milestone uses formal controls; no additional
floating-point simulation is treated as evidence of uniqueness.

Uniqueness holds within the specified global classical periodic class.
Existence for rougher data, spatially varying potentials, nonperiodic boundary
conditions and sharp numerical rates remain outside this result. The sign
convention above is `∂tρ=∂xJ`; `J` is the negative of the current in
`∂tρ+∂xj=0`.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `{inputs['source_sha256']}`.
'''
(root/'COMPLETION_REPORT.md').write_text(report)
plan=(root/'PLAN.md').read_text().replace('Status: implementation in progress.','Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).')
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
    for name,data in sorted(payload.items()):z.writestr('exp012/'+name,data)
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'ZIP CRC failure')
    require(len(z.namelist())==len(set(z.namelist()))==len(payload),'ZIP coverage mismatch')
    for name,data in payload.items():require(z.read('exp012/'+name)==data,'ZIP readback mismatch')
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
