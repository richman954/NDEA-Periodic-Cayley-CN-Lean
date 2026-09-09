import pathlib, subprocess, sys, json
r=pathlib.Path('/content/exp007_check/development')
code='''import pathlib,subprocess,os,time,json,hashlib,datetime
r=pathlib.Path('/content/exp007_check'); d=r/'development';lean=r/'lean-4.31.0-linux/bin/lean'
libs=[d,r/'mathlib/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (r/'mathlib/.lake/packages').iterdir() if p.is_dir()]+[lean.parent.parent/'lib/lean']
env=dict(os.environ,LEAN_PATH=':'.join(map(str,libs)),LEAN_NUM_THREADS='1')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['ReducedClosure']:
 s=d/(name+'.lean'); target=d/(name+'.olean');log=d/('model_'+name+'.log');begin=time.monotonic()
 rec={'source':str(s),'source_sha256_before':sha(s),'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_binary_sha256':sha(lean),'lean_path':env['LEAN_PATH']}
 with log.open('wb') as out:
  try:
   p=subprocess.run([str(lean),'-j','1','-R',str(d),'-o',str(target),str(s)],env=env,stdout=out,stderr=subprocess.STDOUT,timeout=600);rc=p.returncode
  except subprocess.TimeoutExpired:rc=124
 rec.update(exit_code=rc,elapsed_seconds=time.monotonic()-begin,source_sha256_after=sha(s),log_sha256=sha(log),sources_unchanged=sha(s)==rec['source_sha256_before'])
 if rc==0:rec['output_sha256']=sha(target)
 (d/('model_'+name+'_RESULT.json')).write_text(json.dumps(rec,indent=2))
 if rc: break
'''
(r/'model_controller.py').write_text(code)
with (r/'model_controller.log').open('wb') as log:
 p=subprocess.Popen([sys.executable,'-u','-B',str(r/'model_controller.py')],stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid}))
