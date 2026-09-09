"""Fresh-runtime pinned dependency bootstrap; no uploaded Lean artifacts."""
import datetime, hashlib, importlib.util, json, os, pathlib, re, subprocess, sys, time
sys.dont_write_bytecode = True
root=pathlib.Path('/content/exp015_check')
inp=root/'inputs'
out=root/'bootstrap';out.mkdir(exist_ok=False)
env=dict(os.environ,LEAN_NUM_THREADS='1',GIT_TERMINAL_PROMPT='0')
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
record={'passed':False,'commands':[],'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def save():(out/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,cmd,cwd=root,timeout=1200):
    log=out/(str(len(record['commands'])+1).zfill(3)+'_'+label+'.log')
    row={'label':label,'command':list(map(str,cmd)),'log':str(log)}
    record['commands'].append(row);save()
    begin=time.monotonic()
    with log.open('xb') as f:
        r=subprocess.run(row['command'],cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
    row.update(exit_code=r.returncode,elapsed_seconds=time.monotonic()-begin,log_sha256=sha(log));save()
    if r.returncode:raise RuntimeError(label+' failed')
    return log.read_text()
def clone(pin,target):
    target.mkdir(parents=True)
    run('init_'+pin['name'],['git','init','-q',target])
    run('remote_'+pin['name'],['git','-C',target,'remote','add','origin',pin['url']])
    run('fetch_'+pin['name'],['git','-C',target,'fetch','--depth=1','origin',pin['rev']])
    run('checkout_'+pin['name'],['git','-C',target,'checkout','-q','--detach','FETCH_HEAD'])
    require(run('pin_'+pin['name'],['git','-C',target,'rev-parse','HEAD']).strip()==pin['rev'],
        'Dependency pin mismatch: '+pin['name'])
try:
    hashes=json.loads((inp/'INPUT_HASHES.json').read_text())
    require(all(sha(inp/k)==v for k,v in hashes.items()),'Bootstrap input mismatch')
    record['input_hashes']=hashes
    spec=importlib.util.spec_from_file_location('safe_bootstrap',inp/'bootstrap_colab.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    archive=root/'lean-4.31.0-linux.tar.zst'
    run('download_lean',['curl','-fL','--retry','3','--connect-timeout','30','--max-time','900',helper.LEAN_URL,'-o',archive])
    tarpath=root/'lean-4.31.0-linux.tar'
    helper.decompress_zstd(archive,tarpath)
    helper.unpack_toolchain(tarpath,root)
    lean=root/'lean-4.31.0-linux/bin/lean'
    require(sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
        'Compiler pin mismatch')
    record['compiler_sha256']=sha(lean);record['archive_sha256']=sha(archive)
    env['PATH']=str(lean.parent)+':'+env['PATH']
    pins=json.loads((inp/'lake-manifest.json').read_text())['packages']
    paths=[root/'mathlib' if p['name']=='mathlib' else root/'mathlib/.lake/packages'/p['name'] for p in pins]
    # The mathlib root must be materialized before its package subdirectories.
    for pin,path in sorted(zip(pins,paths),key=lambda pair:pair[0]['name']!='mathlib'):clone(pin,path)
    record['dependency_pins']=pins
    cache=out/'cache_client/lib/lean';cache.mkdir(parents=True)
    env['LEAN_PATH']=str(cache)+':'+str(lean.parent.parent/'lib/lean')
    env['LEAN_SRC_PATH']=':'.join(map(str,paths))
    built=set()
    imports=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)',re.M)
    def build(module):
        if module in built:return
        if (lean.parent.parent/'lib/lean'/(module.replace('.','/')+'.olean')).is_file():
            built.add(module);return
        sr,source=next((p,p/(module.replace('.','/')+'.lean')) for p in paths if (p/(module.replace('.','/')+'.lean')).is_file())
        for line in imports.findall(source.read_text()):
            for dep in line.split('--',1)[0].split():build(dep)
        target=cache/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        run('cache_'+module.replace('.','_'),[lean,'-j','1','-R',sr,'-o',target,source],cwd=sr)
        built.add(module)
    build('Cache.Main')
    modules=set(re.findall(r'^import (Mathlib\.\S+)',(inp/'Combined.lean').read_text(),re.M))
    modules.update(['Mathlib.LinearAlgebra.Matrix.Kronecker','Mathlib.Analysis.SpecialFunctions.Exponential','Mathlib.Analysis.Calculus.Deriv.Mul','Mathlib.Analysis.Normed.Algebra.Exponential'])
    # Cache imports are pinned source names, independent of project artifacts.
    modules={m for m in modules if (root/'mathlib'/(m.replace('.','/')+'.lean')).is_file()}
    run('mathlib_cache',[lean,'-j','1','--run',root/'mathlib/Cache/Main.lean','get',*sorted(modules)],cwd=root/'mathlib',timeout=1800)
    record['cache_modules']=sorted(modules)
    record['passed']=True
except Exception as error:
    record['error']=repr(error)
    import traceback;traceback.print_exc()
finally:
    record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({'passed':record['passed'],'error':record.get('error')}),flush=True)
sys.exit(0 if record['passed'] else 1)
