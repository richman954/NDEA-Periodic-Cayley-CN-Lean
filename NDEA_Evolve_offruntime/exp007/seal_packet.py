"""Seal a review packet only after local and independent full verification."""
import datetime,hashlib,importlib.util,json,zipfile
from pathlib import Path
r=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((r/'evidence/FINAL_INPUTS.json').read_text())
localpath=r/'evidence/local_combined/RESULT.json'
remotepath=r/'remote_check/downloaded_evidence/exp007_independent_evidence/final_verification/RESULT.json'
local=json.loads(localpath.read_text());remote=json.loads(remotepath.read_text())
transfer=json.loads((r/'remote_check/FINAL_TRANSFER_CHECK.json').read_text())
assert local['passed'] and remote['passed'] and transfer['passed']
assert local['source_sha256_before']==local['source_sha256_after']==remote['source_sha256_before']==remote['source_sha256_after']==inputs['source_sha256']
assert local['axiom_audits']==remote['axiom_audits'] and set(local['axiom_audits'])==set(inputs['expected_audits'])
assert len(inputs['expected_audits'])==88
assert all(set(v)<= {'propext','Classical.choice','Quot.sound'} for v in local['axiom_audits'].values())
assert all(sha(r/k)==v for k,v in inputs['source_hashes'].items())
spec=importlib.util.spec_from_file_location('audit',r/'verification_tools/verify_exp005.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
for result,path in [(local,localpath),(remote,remotepath)]:
    log=path.parent/'combined.log'
    assert sha(log)==result['log_sha256']
    assert {k:sorted(v) for k,v in audit.validate_axiom_log(log.read_text(),set(inputs['expected_audits'])).items()}==result['axiom_audits']
modules=['ReducedNoncommuting','SpinorGrid','ContinuumSpinor','ReducedClosure','FullClosure','StageBridge','Controls']
receipts={}
for name in modules:
    for p in sorted((r/'evidence').glob('2026*_'+name+'.json')):
        d=json.loads(p.read_text())
        if d.get('exit_code')==0 and d.get('sources_unchanged') and d['source_sha256_after']==sha(r/'lean'/(name+'.lean')):
            assert sha(Path(d['log']))==d['log_sha256']
            receipts[name]=str(p.relative_to(r))
assert set(receipts)==set(modules)
numeric=json.loads((r/'evidence/numerical_checks.json').read_text())
preserve=json.loads((r/'evidence/PREDECESSOR_PRESERVATION.json').read_text())
cross=json.loads((r/'evidence/CROSS_ENVIRONMENT_DEPENDENCIES.json').read_text())
assert numeric['passed'] and preserve['passed']
assert cross['same_module_artifact_paths'] and cross['identical_artifact_hashes']==9868
record={'passed':True,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_sha256':inputs['source_sha256'],'production_theorems':81,'controls':7,'total_audits':88,
    'local_result':str(localpath.relative_to(r)),'local_result_sha256':sha(localpath),
    'independent_result':str(remotepath.relative_to(r)),'independent_result_sha256':sha(remotepath),
    'local_elapsed_seconds':local['elapsed_seconds'],'independent_elapsed_seconds':remote['elapsed_seconds'],
    'local_modular_receipts':receipts,'independent_transfer_checked':True,
    'dependency_artifacts_per_combined_run':local['dependency_artifacts'],
    'identical_cross_environment_dependency_hashes':cross['identical_artifact_hashes'],
    'qualification':'All project source re-elaborated. Pinned compatible external library artifacts reused; Lean and Mathlib were not rebuilt from source.',
    'scope':'One spatial Fourier mode with noncommuting constant internal matrices; arbitrary numerical grid initialization retained through its initial error.'}
(r/'evidence/FINAL_VERIFICATION.json').write_text(json.dumps(record,indent=2)+'\n')
s=(r/'REPORT_DRAFT.md').read_text()
start=s.index('The model is')
s='# Experiment 007 — verified noncommuting periodic spinor closure\n\n'+\
  'Completed September 8, 2026. **Local and independent combined verification passed all 88 audits: 81 production theorems and seven controls.**\n\n'+s[start:]
s=s.replace('Its integrated target theorem','Its proved error theorem').replace('implements\nthe exact equality','proves\nthe exact equality')
start=s.index('At the snapshot time,')
end=s.index('[Numerical diagnostics]',start)
verification='''The seven new modules passed separately both locally and in the fresh Colab
runtime. The final combined checks re-elaborated the complete frozen foundation
and every new proof, using only isolated external library artifacts. All 88
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

'''+f"Local combined check: **{local['elapsed_seconds']:.3f} seconds**. Independent combined check: **{remote['elapsed_seconds']:.3f} seconds**, completed `{remote['end_utc']}`. Each run checked {local['dependency_artifacts']:,} external artifact hashes before and after. Exact reconstruction of the combined source and complete audit catalog passed.\n\n"+\
'''All 9,868 external artifact hashes also agree between the two environments.
The independent runtime downloaded the pinned compiler and compatible library
cache itself. No locally built project artifacts were uploaded. Lean and
Mathlib themselves were not rebuilt from scratch. External compiled libraries
remain the stated trust boundary.

| Module | Successful local receipt |
| --- | --- |
'''+''.join(f'| {name} | [receipt]({path}) |\n' for name,path in receipts.items())+\
'\nThe final qualification is recorded in [FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json), with the [local complete result](evidence/local_combined/RESULT.json) and [independent complete result](remote_check/downloaded_evidence/exp007_independent_evidence/final_verification/RESULT.json).\n\n'
s=s[:start]+verification+s[end:]
s=s.replace('Their\nfinal integration qualification remains pending with the other endpoint files.',
    'All seven controls passed the final combined audit.')
s+='\nThe [convergence figure](evidence/exp007_convergence.png) visualizes the supporting diagnostics. [REPRODUCE.md](REPRODUCE.md) describes the pinned environment and standalone verification command.\n\nCombined source SHA-256: `'+inputs['source_sha256']+'`.\n'
(r/'COMPLETION_REPORT.md').write_text(s)
(r/'PLAN.md').write_text('# Experiment 007 — completed\n\nAll five obligations from the implementation plan are complete: continuum PDE derivatives; uniform noncommuting local error; actual wrapped-grid Cayley bridge and physical norm; full-grid convergence and exact Exp005 stage budget; local/independent combined audits, controls, and preserved evidence.\n\nSee [COMPLETION_REPORT.md](COMPLETION_REPORT.md) for the proved result, scope, validation, and reproduction instructions.\n')
allowed_top={'COMPLETION_REPORT.md','REPRODUCE.md','PLAN.md','make_combined.py','verify_combined.py','numerical_checks.py','run_lean.py','seal_packet.py'}
selected=[]
for p in sorted(r.rglob('*')):
    if not p.is_file() or p.is_symlink():continue
    rel=p.relative_to(r)
    if any(part in {'build','dependencies','__pycache__'} for part in rel.parts):continue
    if rel.parts[0]=='lean' and p.stem not in modules+['Exp007Combined']:continue
    if rel.parts[0] not in {'lean','foundation','verification_tools','evidence','remote_check'} and str(rel) not in allowed_top:continue
    if p.name in {'FINAL_PACKET_RECEIPT.json','PACKET_MANIFEST.json'}:continue
    selected.append(p)
hashes={str(p.relative_to(r)):sha(p) for p in selected}
manifest=r/'PACKET_MANIFEST.json';manifest.write_text(json.dumps(hashes,indent=2)+'\n')
name='Exp007_Verified_Review_Packet_20260908'
archive=r.parent.parent/(name+'.zip')
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in selected+[manifest]:z.write(p,name+'/'+str(p.relative_to(r)))
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert set(z.namelist())=={name+'/'+k for k in hashes}|{name+'/PACKET_MANIFEST.json'}
    assert all(hashlib.sha256(z.read(name+'/'+k)).hexdigest()==v for k,v in hashes.items())
packet={'passed':True,'archive':str(archive),'archive_sha256':sha(archive),'archive_bytes':archive.stat().st_size,
        'manifest_entries':len(hashes),'manifest_sha256':sha(manifest),'verified_file_count':len(hashes)+1}
(r/'evidence/FINAL_PACKET_RECEIPT.json').write_text(json.dumps(packet,indent=2)+'\n')
archive.with_suffix('.zip.sha256').write_text(packet['archive_sha256']+'  '+archive.name+'\n')
print(json.dumps(packet,indent=2))
