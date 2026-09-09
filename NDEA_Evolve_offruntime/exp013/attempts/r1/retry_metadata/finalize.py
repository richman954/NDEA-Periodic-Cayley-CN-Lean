"""Qualify completed checks and seal a checksum-verified Experiment 013 packet."""
import datetime, hashlib, importlib.util, json, os, subprocess, sys, zipfile
from pathlib import Path

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def write_json(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
stamp=datetime.datetime.now(datetime.timezone.utc)
archive=Path('/home/richman954')/f'Exp013_Verified_Review_Packet_{stamp:%Y%m%d}.zip'
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
require(transfer['source_sha256']==inputs['source_sha256']==sha(root/'lean/Exp013Combined.lean'),
    'Final source changed')
spec=importlib.util.spec_from_file_location('generator',root/'make_combined.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
combined,reconstructed=gen.build(root)
require(combined==(root/'lean/Exp013Combined.lean').read_text() and reconstructed==inputs,
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
    if name.endswith('Exp012Foundation.lean'):continue
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
archives=[(Path('/home/richman954/Exp012_Verified_Review_Packet_20260908.zip'),
    baseline['exp012_packet_sha256'])]
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
    'qualification':'Generic complex Hilbert-valued periodic Schrödinger energy balance with arbitrary space/time Hermitian bounded potentials and forcing, homogeneous mass conservation, and uniqueness for shared forcing. The concrete legacy numerical convergence is preserved through an exact predicate bridge. This is conditional classical-solution theory, not general variable-potential existence or numerical convergence. Compiler and compatible external artifacts are trusted inputs.'}
write_json(root/'evidence/FINAL_VERIFICATION.json',record)
report=f'''# Experiment 013 — generic periodic Schrödinger energy and uniqueness

Completed {stamp.date().isoformat()}. All **{record['audits']} new public theorem/control
audits** passed locally and independently on a distinct fresh Colab CPU VM,
with only `propext`, `Classical.choice`, and `Quot.sound`. All {len(modules)} new
modules passed separately.

The reusable framework applies to functions with values in any complex Hilbert
space H, any positive spatial period L, time/space dependent Hermitian
operators V(t,x), and forcing f(t,x). Each V(t,x) is bounded; no uniform
operator-norm bound is assumed:

```text
i ∂t u = −∂xx u + V(t,x)u + f(t,x).
```

The classical predicate requires the actual first time and first/second space
derivatives, their specified joint continuity, periodicity, and the pointwise
PDE. No Fourier representation, energy law, global time bound, finite fiber
dimension, or continuity/periodicity assumption on V or f is added. These are
conditional results about solutions satisfying the classical predicate.

The proof derives the local and integral identities

```text
ρ = ‖u‖²,  J = 2 Re⟨u, i ∂x u⟩,  W = 2 Re⟨u, −i f⟩,
∂t ρ = ∂x J + W,
d/dt ∫[b,b+L] ‖u(t,x)‖² dx = ∫[b,b+L] W(t,x) dx.
```

Continuity of W follows from the difference of the actual density and flux
derivatives. A compact local time-space rectangle justifies differentiation
of the scalar integral. Periodicity cancels the boundary flux. Here energy
means squared L² norm (mass) for L>0, not Hamiltonian expectation. The balance
and conservation identities also hold for arbitrary real L when their
integrals are understood as oriented interval integrals.

For zero forcing this mass is conserved for all real times and interval bases.
For two solutions with the same V and forcing, their difference solves the
homogeneous equation, so their squared L² distance is conserved. When L>0,
matching data at any one real time imply equality at every real time and
position. Positivity and continuity convert zero integral energy into pointwise
equality, including interval endpoints.

The exact legacy predicate bridge recovers the previous two-component model
and identifies the earlier uniformly convergent numerical reconstruction with
its unique classical solution under the unchanged data and mesh assumptions.
Generic files import Mathlib directly; their reuse does not require importing
the concrete predecessor experiments.

The exact controls include the nonzero nonconstant stationary scalar solution
u(x)=2+sin(x) with V(x)=−sin(x)/(2+sin(x)), and the forced solution u(t,x)=t,
V=0, f=i. They check genuine spatial dependence and active potential, the
forcing-work sign, and failure of integral separation when the period is zero.

| Accepted check | Result |
|---|---|
| New modular sources | {len(modules)} passed; [receipts](evidence/FINAL_VERIFICATION.json) |
| Local combined source | {record['audits']} audits; exit 0; {local['elapsed_seconds']:.3f} seconds |
| Independent combined source | {record['audits']} audits; exit 0; {remote['elapsed_seconds']:.3f} seconds |
| Source/catalog | Reconstructed exactly and unchanged during both checks |
| External artifact hashes | {transfer['dependency_artifacts_agree']:,} agree across environments |
| Evidence transfer | {transfer['verified_payload_files']} payload hashes and compiler audits verified |
| Predecessors | Sealed manifests and Exp012 packet preserved |

The distinct CPU session is `exp013-independent-check`, initially empty at
`/content/exp013_check`. Compiler and compatible external libraries were
independently downloaded. Project artifacts were excluded from both combined
import paths; retained predecessor proof bodies were re-elaborated. Lean
4.31.0 and compatible library artifacts remain trusted inputs and were not
rebuilt from source.

This opens a reusable analytic interface for later variable-potential existence,
residual/forcing estimates, and approximation theory. Those general existence,
rough-data spatial L² evolution, forcing norm estimates, sharper rates, and
variable-potential numerical convergence results are not claimed here. Current
numerical convergence remains specialized to the earlier concrete model.

Read [derivation](MATHEMATICAL_DERIVATION.md), [review](REVIEW.md),
[reproduction](REPRODUCE.md), and [saved files](SAVED_FILES.md).

Combined SHA-256: `{inputs['source_sha256']}`.
'''
(root/'COMPLETION_REPORT.md').write_text(report)
plan=(root/'PLAN.md').read_text().replace('Status: implementation in progress; no completed proof claim.','Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).')
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
    for name,data in sorted(payload.items()):z.writestr('exp013/'+name,data)
with zipfile.ZipFile(archive) as z:
    require(z.testzip() is None,'ZIP CRC failure')
    require(len(z.namelist())==len(set(z.namelist()))==len(payload),'ZIP coverage mismatch')
    for name,data in payload.items():require(z.read('exp013/'+name)==data,'ZIP readback mismatch')
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
