"""Check retained declarations and historical positive/rejection controls."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,re,subprocess,sys,time

sys.dont_write_bytecode=True
root=Path('/content/exp008_check');source=root/'historical_source'
work=root/'historical_verification';work.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
record={'passed':False,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'runner_sha256':sha(Path(__file__)),'checks':[]}
def save():(work/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
save()
try:
    final=json.loads((root/'final_verification/RESULT.json').read_text())
    require(final.get('passed') is True,'Exact sealed combined check has not passed')
    require(json.loads((root/'EXTRA_IMPORTS.json').read_text())['exit_code']==0,
            'Full historical library cache incomplete')
    inputs=json.loads((source/'SUITE_INPUTS.json').read_text())
    record['inputs_sha256']=sha(source/'SUITE_INPUTS.json')
    record['source_hashes']=inputs['source_files']
    def check_sources():
        require(all(sha(source/n)==v for n,v in inputs['source_files'].items()),'Suite input changed')
        require(sha(source/'SUITE_INPUTS.json')==record['inputs_sha256'],'Suite catalog changed')
    check_sources()
    checker=root/'final_source/verification_tools/verify_exp005.py'
    require(sha(checker)=='fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb','Audit helper mismatch')
    spec=importlib.util.spec_from_file_location('audit',checker)
    audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
    imports=set()
    require(len({case['name'] for case in inputs['checks']})==len(inputs['checks']),'Duplicate check name')
    for case in inputs['checks']:
        p=source/case['file'];require(sha(p)==case['source_sha256'],'Check source pin mismatch')
        audit.scan_proof_policy(p.read_text());clean=audit.code_only(p.read_text())
        found=re.findall(r'^import (\S+)',clean,re.M)
        require(all(m=='Mathlib' or m.startswith(('Mathlib.','Lean.','Std.','Init.')) for m in found),
                'Historical project import found')
        imports.update(found)
        names=re.findall(r'^#print axioms (\S+)',clean,re.M)
        require(len(names)==len(set(names)) and set(names)==set(case['expected_audits']),
                'Declared audit coverage mismatch: '+case['name'])
    lean=root/'lean-4.31.0-linux/bin/lean';mathlib=root/'mathlib'
    require(sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Compiler pin mismatch')
    record['compiler_sha256']=sha(lean)
    pins=json.loads((root/'final_source/remote_check/bootstrap_inputs/lake-manifest.json').read_text())['packages']
    paths=[mathlib if p['name']=='mathlib' else mathlib/'.lake/packages'/p['name'] for p in pins]
    def check_packages():
        for pin,path in zip(pins,paths):
            head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
            dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain=v1','--untracked-files=no'],text=True)
            require(head==pin['rev'] and not dirty,'Dependency checkout changed: '+pin['name'])
    check_packages();record['dependency_pins']=pins
    helper=root/'final_source/verification_tools/lean_import_closure.py'
    require(sha(helper)=='12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057','Import walker mismatch')
    library=work/'dependencies';cmd=[sys.executable,'-B',str(helper)]
    for path in paths:cmd+=['--root',str(path),'--artifact-root',str(path/'.lake/build/lib/lean')]
    cmd+=['--copy-artifacts-to',str(library),'--report-artifact-bytes',*sorted(imports)]
    with (work/'dependency_copy.log').open('xb') as log:
        subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    def libhashes():return {str(p.relative_to(library)):sha(p) for p in sorted(library.rglob('*')) if p.is_file()}
    hashes=libhashes();require(bool(hashes),'Empty isolated library')
    require(not any(n.startswith('NDEAEvolve/') for n in hashes),'Project artifact copied')
    manifest=work/'DEPENDENCY_ARTIFACTS.json';manifest.write_text(json.dumps(hashes,indent=2)+'\n')
    record['dependency_artifacts']=len(hashes);record['dependency_manifest_sha256']=sha(manifest)
    record['external_imports']=sorted(imports)
    env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(library)+':'+str(lean.parent.parent/'lib/lean'))
    for key in ['LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
    record['lean_path']=env['LEAN_PATH'];save()
    for case in inputs['checks']:
        p=source/case['file'];log=work/(case['name']+'.log')
        cmd=[str(lean),'-j','1',str(p)]
        row={'name':case['name'],'file':case['file'],'expectation':case['expectation'],
             'passed':False,'source_sha256_before':sha(p),'command':cmd}
        record['checks'].append(row);save();begin=time.monotonic()
        with log.open('xb') as out:
            process=subprocess.run(cmd,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=1200)
        row.update(exit_code=process.returncode,elapsed_seconds=time.monotonic()-begin,
                   source_sha256_after=sha(p),log_sha256=sha(log))
        require(row['source_sha256_before']==row['source_sha256_after']==case['source_sha256'],'Checked source changed')
        content=log.read_text()
        errors=[{'file':m[0],'line':int(m[1]),'column':int(m[2]),'message':m[3]}
                for m in re.findall(r'^(.+):(\d+):(\d+): error: ([^\n]*)',content,re.M)]
        row['errors']=errors
        if case['expectation']=='pass':
            require(process.returncode==0,'Positive source check failed: '+case['name'])
            rows=audit.validate_axiom_log(content,set(case['expected_audits']))
            row['axiom_audits']={k:sorted(v) for k,v in rows.items()}
        elif case['expectation']=='reject':
            require(process.returncode==1,'Expected ordinary Lean proof rejection: '+case['name'])
            require(not case['expected_audits'],'Rejection driver must not claim accepted theorem audits')
            require(len(errors)==case['expected_error_count'],'Unexpected rejection diagnostic count')
            require([e['line'] for e in errors]==case['expected_error_lines'],
                    'Rejection locations differ from the accepted control diagnostics')
            require(all(fragment in content for fragment in case['expected_diagnostic_fragments']),
                    'Expected false-claim diagnostic fragment missing')
            for error in errors:
                require(Path(error['file'])==p,'Rejection arose in another file')
                require(any(lo<=error['line']<=hi for lo,hi in case['error_line_ranges']),
                        'Rejection arose outside intended false-control proof')
                require(any(re.search(pattern,error['message']) for pattern in case['allowed_diagnostic_patterns']),
                        'Unexpected rejection reason: '+error['message'])
            require(not re.search(r'unknown module|object file .* does not exist|unknown identifier|failed to synthesize|maximum recursion|maximum number of heartbeats|out of memory|PANIC',content,re.I),
                    'Rejection caused by environment or resource failure')
            require(not re.search(r'depends on axioms|does not depend on any axioms',content),
                    'Unexpected audit output in rejection driver')
            row['axiom_audits']={}
        else:raise RuntimeError('Unknown check expectation')
        row['passed']=True;save()
    check_sources();require(hashes==libhashes(),'Isolated library artifacts changed')
    check_packages();record['passed']=True
except Exception as error:
    record['error']=repr(error)
    import traceback;traceback.print_exc()
finally:
    record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({'passed':record['passed'],'checks_completed':sum(c['passed'] for c in record['checks']),
                      'error':record.get('error')}),flush=True)
sys.exit(0 if record['passed'] else 1)
