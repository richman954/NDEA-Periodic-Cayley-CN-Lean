"""Launch a source-pinned independent modular batch; input is uploaded separately."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path('/content/exp008_check')
request=json.loads((root/'MODULE_UPLOAD.json').read_text())
request_hash=hashlib.sha256((root/'MODULE_UPLOAD.json').read_bytes()).hexdigest()
job=root/('run_modules_'+request['batch']+'.py')
code=r'''
from pathlib import Path,PurePosixPath
import datetime,hashlib,json,os,shutil,subprocess,tarfile,time
root=Path('/content/exp008_check')
request=REQUEST
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archive=Path(request['archive'])
if sha(archive)!=request['sha256']:raise RuntimeError('Source archive mismatch')
if not json.loads((root/'development/evidence/FOUNDATION_RESULT.json').read_text())['passed']:
    raise RuntimeError('Independent foundation not yet passed')
work=root/'development/batches'/request['batch'];source=work/'source';lib=work/'lib'
source.mkdir(parents=True,exist_ok=False);lib.mkdir()
files={}
with tarfile.open(archive) as tar:
    for item in tar.getmembers():
        p=PurePosixPath(item.name)
        if not item.isfile() or len(p.parts)!=1 or item.name in files or p.suffix!='.lean':
            raise RuntimeError('Unsafe or duplicate source member')
        files[item.name]=tar.extractfile(item).read()
if {k:hashlib.sha256(v).hexdigest() for k,v in files.items()}!=request['source_hashes']:
    raise RuntimeError('Source pin coverage mismatch')
for name,data in files.items():(source/name).write_bytes(data)
lean=root/'lean-4.31.0-linux/bin/lean';mathlib=root/'mathlib'
paths=[lib,root/'development/lib',mathlib/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (mathlib/'.lake/packages').iterdir() if p.is_dir()]+[lean.parent.parent/'lib/lean']
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=':'.join(map(str,paths)))
env.pop('LEAN_SRC_PATH',None)
record={'passed':False,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'request':request,'modules':[],'compiler_sha256':sha(lean),'lean_path':env['LEAN_PATH']}
def save():(work/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
save()
try:
    for name in request['modules']:
        src=source/(name+'.lean');target=lib/(name+'.olean');log=work/(name+'.log')
        before=sha(src);cmd=[str(lean),'-j','1','-R',str(source),'-o',str(target),str(src)]
        begin=time.monotonic()
        with log.open('xb') as out:
            result=subprocess.run(cmd,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=900)
        row={'module':name,'command':cmd,'source_sha256_before':before,'source_sha256_after':sha(src),'exit_code':result.returncode,'elapsed_seconds':time.monotonic()-begin,'log_sha256':sha(log)}
        record['modules'].append(row);save()
        if result.returncode or before!=sha(src):raise RuntimeError('Module failed: '+name)
        for compiled in lib.glob(name+'.*'):
            if compiled.is_file():shutil.copyfile(compiled,root/'development/lib'/compiled.name)
    record['passed']=True
except Exception as error:
    record['error']=repr(error)
    import traceback;traceback.print_exc()
finally:
    record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({'passed':record['passed'],'error':record.get('error'),'batch':request['batch']}),flush=True)
'''.replace('REQUEST',repr(request))
job.write_text(code)
with (root/('modules_'+request['batch']+'_controller.log')).open('xb') as log:
    p=subprocess.Popen([sys.executable,'-u','-B',str(job)],stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print(json.dumps({'pid':p.pid,'batch':request['batch'],'request_sha256':request_hash}))
