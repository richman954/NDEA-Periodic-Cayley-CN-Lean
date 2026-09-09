"""Qualify completed checks and seal a checksum-verified Experiment 010 packet."""
import datetime, hashlib, importlib.util, json, os, subprocess, sys, zipfile
from pathlib import Path

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def write_json(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
stamp=datetime.datetime.now(datetime.timezone.utc)
archive=Path('/home/richman954')/f'Exp010_Verified_Review_Packet_{stamp:%Y%m%d}.zip'
require(not archive.exists() and not (root/'PACKET_MANIFEST.json').exists(),
    'Packet or sealed manifest already exists; preserve it before any writes')
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
transfer=json.loads((root/'remote_check/FINAL_TRANSFER_CHECK.json').read_text())
local=json.loads((root/'evidence/local_combined/RESULT.json').read_text())
remote_root=root/'remote_check/downloaded_evidence'
remote=json.loads((remote_root/'final_verification/RESULT.json').read_text())
numeric=json.loads((root/'evidence/numerical_checks.json').read_text())
for name,result in [('transfer',transfer),('local',local),('independent',remote),('numeric',numeric)]:
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
require(numeric['script_sha256']==sha(root/'numerical_checks.py'),'Numerical source changed')
require(transfer['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp010Combined.lean'),
    'Final source changed')
spec=importlib.util.spec_from_file_location('generator',root/'make_combined.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
combined,reconstructed=gen.build(root)
require(combined==(root/'lean/Exp010Combined.lean').read_text() and reconstructed==inputs,
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
    if name.endswith('Exp009Foundation.lean'):continue
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
archives=[(Path('/home/richman954/Exp009_Verified_Review_Packet_20260908.zip'),
    baseline['exp009_review_archive_sha256'])]
for p,digest in archives:require(sha(p)==digest,'Earlier archive changed: '+p.name)
record={'passed':True,'utc':stamp.isoformat(),'source_sha256':inputs['source_sha256'],
    'source_hashes':inputs['source_hashes'],'expected_audits':inputs['expected_audits'],
    'audits':len(inputs['expected_audits']),'accepted_modular_receipts':modules,
    'local_result_sha256':sha(root/'evidence/local_combined/RESULT.json'),
    'independent_result_sha256':sha(remote_root/'final_verification/RESULT.json'),
    'transfer_receipt_sha256':sha(root/'remote_check/FINAL_TRANSFER_CHECK.json'),
    'independent_archive_sha256':transfer['archive_sha256'],
    'bootstrap_verification':transfer['bootstrap_verification'],
    'numeric_result_sha256':sha(root/'evidence/numerical_checks.json'),
    'review_receipt_sha256':sha(root/'evidence/REVIEW_CHECK.json'),
    'predecessor_receipt_sha256':sha(root/'evidence/PREDECESSOR_PRESERVATION.json'),
    'qualification':'Classical periodic spinor PDE solution under a summable second weighted coefficient moment, actual sampled grid error bound and convergence at common time one. Compiler and compatible external library artifacts are trusted inputs.'}
write_json(root/'evidence/FINAL_VERIFICATION.json',record)
report=f'''# Experiment 010 — verified classical infinite Fourier solution

Completed {stamp.date().isoformat()}. All **{record['audits']} new public theorem/control
audits** passed locally and independently on a fresh Colab CPU VM, with only
`propext`, `Classical.choice`, and `Quot.sound`. All {len(modules)} new modules passed
separately.

For coefficient sequences satisfying `A₂=Σ_m (1+|m|)² ‖a_m‖<∞`, the actual
infinite Fourier reference from Experiment 009 now has its time derivative,
first spatial derivative, and second spatial derivative proved. All four
quantities `U`, `Ut`, `Ux`, and `Uxx` are jointly continuous. The solution is
periodic with period `2π` and satisfies `iUt=-Uxx+(Z+X)U` pointwise.
The actual derivative exchanges are derived from summable uniform bounds.

The theorem `infiniteSolution_classical` constructs an explicit predicate with
derivative-existence fields. An exact control supplies coefficients nonzero at
every signed frequency, satisfying the regularity condition and producing a
classical solution. This applies beyond finite Fourier sums.

The new grid endpoints compare the numerical iterate with pointwise samples of
this classical solution. With the predecessor's cutoff, grid and step restrictions,

```text
e_N ≤ e_0 + √(2π) [ T(Ct(M)k²+Cs(M)h²)A + 2A₂/(M+1)² ],
A=Σ_m ‖a_m‖, Ct(M)=1000(M²+2)³, Cs(M)=M⁴/8.
```

The required restrictions are `M≥1`, `d>2M`, `dh=2π`, `h>0`, `Mh≤1`,
`k≥0`, `2k(M²+2)≤1`, and `Nk≤T`. The proved schedule
`M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`
gives convergence of sampled error at exactly `T=1` when initial sampled error
tends to zero. Exact sampled initialization is included. The cutoff-dependent
constants remain explicit; no universal second-order mesh rate is claimed.

| Accepted check | Result |
|---|---|
| New modular sources | {len(modules)} passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | {record['audits']} audits; exit 0; {local['elapsed_seconds']:.3f} seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | {record['audits']} audits; exit 0; {remote['elapsed_seconds']:.3f} seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly and unchanged during both checks |
| External library hashes | {transfer['dependency_artifacts_agree']:,} agree across environments |
| Evidence transfer | {transfer['verified_payload_files']} payload hashes verified; uploaded inputs and compiler audits matched |
| Earlier experiments | Sealed predecessor manifests and the latest Exp009 ZIP preserved |

The fresh CPU session is `exp010-independent-check`, with an initially empty
project workspace at `/content/exp010_check`. Its compiler and libraries were
downloaded independently. No project build artifacts were uploaded or available
on either final combined import path. The predecessor proof bodies retained in
the frozen Experiment 009 combined source were re-elaborated.

Lean 4.31.0 and compatible compiled external libraries remain trusted inputs.
The checks pin compiler/source revisions and compare artifact hashes; they do
not rebuild Lean or Mathlib or prove source-to-artifact correspondence.

Supporting [floating-point diagnostics](NUMERICAL_DIAGNOSTICS.md) compare
analytic derivatives with centered finite differences, bound omitted Fourier
derivative tails, check the PDE, and reject wrong signs and omitted potentials.
Their analytic truncation estimates do not certify floating-point roundoff.

The second weighted absolute moment is a sufficient regularity hypothesis.
Variable spatial potentials, uniqueness, interpolation convergence, rougher
coefficient classes, and universal second-order rates for arbitrary infinite
data remain outside the result.

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
    for name,data in sorted(payload.items()):z.writestr('exp010/'+name,data)
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'ZIP CRC failure')
    require(len(z.namelist())==len(set(z.namelist()))==len(payload),'ZIP coverage mismatch')
    for name,data in payload.items():require(z.read('exp010/'+name)==data,'ZIP readback mismatch')
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
