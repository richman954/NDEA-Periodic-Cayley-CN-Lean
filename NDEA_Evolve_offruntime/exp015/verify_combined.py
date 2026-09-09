"""Re-elaborate project source using recorded compatible external artifacts."""
import argparse,datetime,hashlib,importlib.util,json,os,re,subprocess,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
p.add_argument('--lean',type=Path,required=True)
p.add_argument('--mathlib',type=Path,required=True)
p.add_argument('--other-packages',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();root=a.root.resolve();work=a.output.resolve();work.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,m):
    if not b:raise RuntimeError(m)
record={'passed':False,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'runner_sha256':sha(Path(__file__)),'scope':'Experiment 015 sources and the exact retained Experiment 014 combined proof bodies, including its generic Experiment 013 foundation re-elaborated using compatible external artifacts from pinned source checkouts, with recorded hashes. Earlier numerical proof chains are outside this combined source. Compiler and library artifacts remain trusted inputs; this check does not rebuild them or prove source-to-artifact correspondence.'}
def save():(work/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
try:
    inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
    source=root/'lean/Exp015Combined.lean'
    require(sha(source)==inputs['source_sha256'],'Combined source mismatch')
    require(all(sha(root/k)==v for k,v in inputs['source_hashes'].items()),'Source pin mismatch')
    generator=root/'make_combined.py'
    require(sha(generator)==inputs['generator_sha256'],'Generator pin mismatch')
    gen_spec=importlib.util.spec_from_file_location('combined_generator',generator)
    gen=importlib.util.module_from_spec(gen_spec);gen_spec.loader.exec_module(gen)
    rebuilt,rebuilt_inputs=gen.build(root)
    require(rebuilt==source.read_text() and rebuilt_inputs==inputs,
            'Combined source or complete audit catalog differs from reconstruction')
    record['reconstruction_verified']=True
    record['source_sha256_before']=sha(source);record['source_hashes']=inputs['source_hashes']
    require(sha(a.lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Compiler pin mismatch')
    record['compiler_sha256']=sha(a.lean)
    checker=root/'verification_tools/verify_exp005.py'
    require(sha(checker)=='fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb','Audit checker mismatch')
    spec=importlib.util.spec_from_file_location('proof_audit',checker)
    audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
    audit.scan_proof_policy(source.read_text())
    clean=audit.code_only(source.read_text())
    imports=re.findall(r'^import (\S+)',clean,re.M)
    require(imports==inputs['external_imports'],'External imports mismatch')
    require(all(m.startswith(('Mathlib.','Lean.','Std.','Init.')) for m in imports),'Project import found')
    names=re.findall(r'^#print axioms (\S+)',clean,re.M)
    require(len(names)==len(set(names)) and names==inputs['expected_audits'],'Audit declarations mismatch')
    lockfile=root/'remote_check/bootstrap_inputs/lake-manifest.json'
    require(sha(lockfile)=='8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158',
            'Frozen dependency lock mismatch')
    pins=json.loads(lockfile.read_text())['packages']
    packages=[a.mathlib if pin['name']=='mathlib' else a.other_packages/pin['name'] for pin in pins]
    def package_state():
        for pin,path in zip(pins,packages):
            head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain=v1','--untracked-files=no'],text=True)
            require(head==pin['rev'] and not dirty,'Dependency source changed: '+pin['name'])
    package_state();record['dependency_pins']=pins
    helper=root/'verification_tools/lean_import_closure.py'
    require(sha(helper)=='12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057',
            'Dependency walker mismatch')
    library=work/'dependencies'
    cmd=[sys.executable,'-B',str(helper)]
    for path in packages:cmd+=['--root',str(path),'--artifact-root',str(path/'.lake/build/lib/lean')]
    cmd+=['--copy-artifacts-to',str(library),'--report-artifact-bytes',*imports]
    with (work/'dependency_copy.log').open('xb') as log:
        subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    project_modules={Path(name).stem for name in inputs['source_hashes']}|{'Exp015Combined'}|gen.EMBEDDED_PREDECESSOR_MODULES
    require(not (library/'NDEAEvolve').exists() and
            not any((library/(module+suffix)).exists() for module in project_modules
                    for suffix in ['.olean','.ilean','.ir']),
            'Project artifacts copied')
    def libhashes():return {str(p.relative_to(library)):sha(p) for p in sorted(library.rglob('*')) if p.is_file()}
    hashes=libhashes();require(bool(hashes),'Empty dependency library')
    manifest=work/'DEPENDENCY_ARTIFACTS.json';manifest.write_text(json.dumps(hashes,indent=2)+'\n')
    record['dependency_artifacts']=len(hashes);record['dependency_manifest_sha256']=sha(manifest)
    env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(library)+':'+str(a.lean.parent.parent/'lib/lean'))
    env.pop('LEAN_SRC_PATH',None)
    env.pop('LEAN_SYSROOT',None)
    cmd=[str(a.lean),'-j','1',str(source)]
    record['command']=cmd;record['lean_path']=env['LEAN_PATH'];save()
    begin=time.monotonic()
    with (work/'combined.log').open('xb') as log:
        result=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
    record['exit_code']=result.returncode;record['elapsed_seconds']=time.monotonic()-begin
    record['log_sha256']=sha(work/'combined.log')
    require(result.returncode==0,'Combined Lean elaboration failed')
    audits=audit.validate_axiom_log((work/'combined.log').read_text(),set(names))
    record['axiom_audits']={k:sorted(v) for k,v in audits.items()}
    record['source_sha256_after']=sha(source)
    require(record['source_sha256_before']==record['source_sha256_after'],'Combined source changed')
    require(all(sha(root/k)==v for k,v in inputs['source_hashes'].items()),'Project source changed')
    require(hashes==libhashes(),'External artifacts changed')
    package_state();record['passed']=True
except Exception as error:
    record['error']=repr(error)
    import traceback;traceback.print_exc()
finally:
    record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({k:record.get(k) for k in ['passed','exit_code','error','elapsed_seconds','dependency_artifacts']}),flush=True)
sys.exit(0 if record['passed'] else 1)
