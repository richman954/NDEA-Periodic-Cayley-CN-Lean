"""Launch one combined Exp006 check against independently downloaded libraries."""
import json
from pathlib import Path
import subprocess
import sys

root=Path('/content/exp006_check')
code=r'''
import datetime,hashlib,importlib.util,json,os,pathlib,re,subprocess,sys,time
sys.dont_write_bytecode=True
root=pathlib.Path('/content/exp006_check')
base=pathlib.Path('/content/exp005_independent_check')
source=root/'CombinedVerification.lean'
inputs=json.loads((root/'FINAL_INPUTS.json').read_text())
work=root/'final_verification';work.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
require=lambda b,m: None if b else (_ for _ in ()).throw(RuntimeError(m))
record={'passed':False,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_sha256_before':sha(source),'expected_audits':inputs['expected_audits'],
        'scope':'Independent combined source elaboration; compatible pinned library artifacts reused.'}
def save(): (work/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
try:
    require(record['source_sha256_before']==inputs['source_sha256'],'Combined source pin mismatch')
    require(json.loads((root/'ADDITIONAL_DEPENDENCIES.json').read_text())['exit_code']==0,'Additional cache bootstrap incomplete')
    checker=base/'verify_exp005.py'
    require(sha(checker)=='fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb','Audit checker mismatch')
    spec=importlib.util.spec_from_file_location('audit_parser',checker)
    audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
    text=source.read_text()
    audit.scan_proof_policy(text)
    clean=audit.code_only(text)
    imports=re.findall(r'^import (\S+)',clean,re.M)
    require(all(m.startswith(('Mathlib.','Lean.','Std.','Init.')) for m in imports),'Unexpected project import')
    names=re.findall(r'^#print axioms (\S+)',clean,re.M)
    require(len(names)==len(set(names))==len(inputs['expected_audits']) and set(names)==set(inputs['expected_audits']),'Audit declarations mismatch')
    lean=base/'lean-4.31.0-linux/bin/lean'
    require(sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Compiler pin mismatch')
    record['compiler_sha256']=sha(lean)
    frozen=base/'evidence/20260908T044513/bootstrap_integrity/source'
    pins=json.loads((frozen/'lake-manifest.json').read_text())['packages']
    packages=[base/'mathlib' if p['name']=='mathlib' else base/'mathlib/.lake/packages'/p['name'] for p in pins]
    record['dependency_pins']=pins
    def check_packages():
        for pin,path in zip(pins,packages):
            head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain=v1','--untracked-files=no'],text=True)
            require(head==pin['rev'] and not dirty,'Dependency source changed: '+pin['name'])
    check_packages()
    helper=frozen/'experiments/exp003_exact_order_defect_norm_bound/assurance/lean_import_closure.py'
    library=work/'dependencies'
    command=[sys.executable,'-B',str(helper)]
    for p in packages: command+=['--root',str(p),'--artifact-root',str(p/'.lake/build/lib/lean')]
    command+=['--copy-artifacts-to',str(library),'--report-artifact-bytes',*imports]
    with (work/'dependency_copy.log').open('xb') as log:
        subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=300)
    require(not (library/'NDEAEvolve').exists(),'Project cache was copied')
    dependency_hashes={str(p.relative_to(library)):sha(p) for p in sorted(library.rglob('*')) if p.is_file()}
    require(bool(dependency_hashes),'Empty dependency cache')
    manifest=work/'DEPENDENCY_ARTIFACTS.json';manifest.write_text(json.dumps(dependency_hashes,indent=2)+'\n')
    record['dependency_artifact_manifest_sha256']=sha(manifest)
    record['dependency_artifacts']=len(dependency_hashes)
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    env['LEAN_PATH']=str(library)+':'+str(lean.parent.parent/'lib/lean')
    env.pop('LEAN_SRC_PATH',None)
    record['lean_path']=env['LEAN_PATH']
    command=[str(lean),'-j','1',str(source)]
    record['command']=command;save()
    begin=time.monotonic()
    with (work/'combined.log').open('xb') as log:
        process=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=900)
    record['exit_code']=process.returncode
    record['elapsed_seconds']=time.monotonic()-begin
    record['log_sha256']=sha(work/'combined.log')
    require(process.returncode==0,'Combined Lean check failed')
    rows=audit.validate_axiom_log((work/'combined.log').read_text(),set(inputs['expected_audits']))
    record['axiom_audits']={k:sorted(v) for k,v in rows.items()}
    record['source_sha256_after']=sha(source)
    require(record['source_sha256_before']==record['source_sha256_after'],'Source changed during compile')
    require(dependency_hashes=={str(p.relative_to(library)):sha(p) for p in sorted(library.rglob('*')) if p.is_file()},'Dependency artifacts changed')
    check_packages()
    record['passed']=True
except Exception as error:
    record['error']=repr(error)
    import traceback;traceback.print_exc()
finally:
    record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({k:record.get(k) for k in ['passed','exit_code','error','elapsed_seconds']}),flush=True)
'''
job=root/'verify_final_exp006.py'
job.write_text(code)
with (root/'final_controller.log').open('xb') as log:
    p=subprocess.Popen([sys.executable,'-u','-B',str(job)],cwd=root,stdout=log,
                       stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid,'root':str(root)}))
