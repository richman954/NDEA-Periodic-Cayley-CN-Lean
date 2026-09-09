import pathlib,subprocess,sys,json
r=pathlib.Path('/content/exp007_check')
(r/'development').mkdir(exist_ok=True)
(r/'development/CombinedVerification.lean').write_bytes((r/'inputs/Exp006CombinedVerification.lean').read_bytes())
code="""import pathlib,subprocess,os,time,json,hashlib
r=pathlib.Path('/content/exp007_check');lean=r/'lean-4.31.0-linux/bin/lean'
libs=[r/'development',r/'mathlib/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (r/'mathlib/.lake/packages').iterdir() if p.is_dir()]+[lean.parent.parent/'lib/lean']
env=dict(os.environ,LEAN_PATH=':'.join(map(str,libs)),LEAN_NUM_THREADS='1')
s=r/'development/CombinedVerification.lean';begin=time.monotonic()
with (r/'development/foundation.log').open('wb') as log:
 p=subprocess.run([str(lean),'-j','1','-R',str(r/'development'),'-o',str(r/'development/CombinedVerification.olean'),str(s)],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=900)
(r/'development/FOUNDATION_RESULT.json').write_text(json.dumps({'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-begin,'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest()},indent=2))
"""
(r/'development/check_foundation.py').write_text(code)
with (r/'development/controller.log').open('wb') as log:
 p=subprocess.Popen([sys.executable,'-u','-B',str(r/'development/check_foundation.py')],stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid}))
