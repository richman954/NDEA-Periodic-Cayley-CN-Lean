"""Qualify completed checks and seal a checksum-verified Experiment 009 packet."""
import datetime, hashlib, importlib.util, json, os, subprocess, sys, zipfile
from pathlib import Path

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def write_json(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
stamp=datetime.datetime.now(datetime.timezone.utc)
archive=Path('/home/richman954')/f'Exp009_Verified_Review_Packet_{stamp:%Y%m%d}.zip'
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
require(numeric['source_sha256']==sha(root/'numerical_checks.py'),'Numerical source changed')
plot=json.loads((root/'evidence/exp009_convergence_receipt.json').read_text())
require(plot.get('passed') is True and plot['input_sha256']==sha(root/'evidence/numerical_checks.json')
    and plot['script_sha256']==sha(root/'plot_convergence.py'),'Plot inputs changed')
for name,digest in plot['output_sha256'].items():
    require(sha(root/'evidence'/name)==digest,'Plotted artifact changed')
require(transfer['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp009Combined.lean'),
    'Final source changed')
spec=importlib.util.spec_from_file_location('generator',root/'make_combined.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
combined,reconstructed=gen.build(root)
require(combined==(root/'lean/Exp009Combined.lean').read_text() and reconstructed==inputs,
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
    if name.endswith('Exp008Foundation.lean'):continue
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
archives=[(Path('/home/richman954/Exp008_Verified_Review_Packet_20260908.zip'),
    baseline['exp008_review_archive_sha256']),
    (Path('/home/richman954/Experiments_001-008_Fresh_VM_Recheck_20260908.zip'),
    baseline['fresh_vm_r2_packet_sha256'])]
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
    'plot_receipt_sha256':sha(root/'evidence/exp009_convergence_receipt.json'),
    'review_receipt_sha256':sha(root/'evidence/REVIEW_CHECK.json'),
    'predecessor_receipt_sha256':sha(root/'evidence/PREDECESSOR_PRESERVATION.json'),
    'qualification':'Infinite absolute-summable Fourier evolution, sampled tail control, and growing-cutoff grid convergence. Classical infinite-series PDE differentiation is outside this result. Compiler and compatible external library artifacts are trusted inputs.'}
write_json(root/'evidence/FINAL_VERIFICATION.json',record)
report=f'''# Experiment 009 — verified infinite Fourier reference and growing cutoff

Completed {stamp.date().isoformat()}. Local and independent Colab combined checks
passed all **{record['audits']} new public theorem/control audits** with only
`propext`, `Classical.choice`, and `Quot.sound`. All {len(modules)} new modules passed
separately. This extends the finite-spectrum reference of Experiment 008 to
coefficients with `A=Σ_m ‖a_m‖<∞`.

The actual infinite reference is
`U(t,x)=Σ_m exp(imx) exp[-it(m²I+Z+X)]a_m`. Its series converges absolutely;
periodicity, initial value, and equality between its samples and the infinite
grid series are proved. The split grid matrices remain the actual noncommuting
centered-difference spinor scheme from the earlier experiments.

For `τ_M=Σ_{{|m|>M}}‖a_m‖`, the new theorem derives

```text
e_N ≤ e_0 + √(2π) [ T(Ct(M)k²+Cs(M)h²)A + 2τ_M ],
Ct(M)=1000(M²+2)³, Cs(M)=M⁴/8.
```

Both errors compare against the full infinite reference. The two tails arise
at the initial and final times; arbitrary numerical initialization retains its
full discrepancy. The sampled tail estimate uses absolute summability, allowing
aliasing of omitted frequencies. The retained band must still satisfy `d>2M`.
Other hypotheses are `M≥1`, `dh=2π`, `h>0`, `Mh≤1`, `k≥0`,
`2k(M²+2)≤1`, and `Nk≤T`.

The generic endpoint proves convergence with `M→∞`, vanishing displayed
consistency cost, and vanishing full-reference initial error. A fully proved
schedule is `M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`.
It satisfies every restriction and reaches time `T=1` exactly. Its consistency
cost is `[(1000/36)(1+2/M²)³+π²/128]/M²`, which tends to zero.
Exact sampled initialization therefore gives convergence to the full reference
at that common final time.

For a summable weighted moment `A_r=Σ_m(1+|m|)^r‖a_m‖`, the proof gives
`τ_M≤A_r/(M+1)^r` and inserts this bound into the actual grid-error theorem.
An exact control exhibits summable coefficients nonzero at every integer
frequency, with positive tails beyond every finite cutoff. Coherent sampled
aliases expose the failure of a naive infinite-grid Parseval estimate.

| Accepted check | Result |
|---|---|
| New modular sources | {len(modules)} passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | {record['audits']} audits; exit 0; {local['elapsed_seconds']:.3f} seconds; [result](evidence/local_combined/RESULT.json) |
| Independent combined source | {record['audits']} audits; exit 0; {remote['elapsed_seconds']:.3f} seconds; [result](remote_check/downloaded_evidence/final_verification/RESULT.json) |
| Source and public catalog | Reconstructed exactly, unchanged during both checks |
| External library hashes | {transfer['dependency_artifacts_agree']:,} agree across environments |
| Evidence transfer | {transfer['verified_payload_files']} payload hashes verified; exact uploaded inputs and compiler audits matched |
| Previous sealed files | All predecessor manifests and both latest original ZIPs preserved |

The Colab check ran on a newly allocated replacement CPU VM, session
`exp009-independent-check`. Its pinned compiler and external libraries were
downloaded independently under `/content/exp009_check`. The earlier
`exp008-fresh-recheck-r2` runtime became unavailable before the Experiment 009
independent proof check; its prepared request and environment records are
preserved in `remote_check/lost_runtime/`. The accepted local proof and earlier
sealed evidence remained intact. No local project build artifacts were
uploaded or available on the final combined import paths. The predecessor
proof bodies retained in the frozen Experiment 008 combined source are
re-elaborated.

Lean 4.31.0 and compatible compiled external libraries remain trusted inputs.
The checks pin compiler/source revisions and compare artifact hashes; they do
not rebuild Lean or Mathlib or prove source-to-artifact correspondence.

Supporting floating-point diagnostics exercise genuine signed infinite
geometric data, exact closed-form sampled initialization, a terminal reference
with an explicit analytic omitted-tail bound, both endpoint tails, perturbed
initialization, the growing schedule, wrapped-grid identities, and coherent
aliasing controls. See [numerical details](NUMERICAL_DIAGNOSTICS.md) and
[data](evidence/numerical_checks.json). The truncation estimate does not certify
floating-point roundoff.
The [convergence figure](evidence/exp009_convergence.pdf) plots these accepted
diagnostics, with its input, script, and output hashes checked.

Absolute summability alone gives this Fourier evolution reference and sampled
grid convergence. Classical time and second-space derivatives of the infinite
series have not been proved here. Spatially varying potentials, numerical
interpolation, and a universal second-order rate for arbitrary infinite data
remain outside the result. The Fourier tail may decay slowly.

See [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
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
    for name,data in sorted(payload.items()):z.writestr('exp009/'+name,data)
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'ZIP CRC failure')
    require(len(z.namelist())==len(set(z.namelist()))==len(payload),'ZIP coverage mismatch')
    for name,data in payload.items():require(z.read('exp009/'+name)==data,'ZIP readback mismatch')
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
