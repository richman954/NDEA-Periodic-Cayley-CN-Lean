import pathlib,tarfile,subprocess,sys,json
root=pathlib.Path('/content/exp007_check');root.mkdir(exist_ok=True)
inp=root/'inputs';inp.mkdir(exist_ok=True)
with tarfile.open('/content/exp007_bootstrap_inputs.tar.gz') as tar:
 for m in tar.getmembers():
  assert m.isfile() and '/' not in m.name and m.name not in ('.','..')
 tar.extractall(inp,filter='data')
with (root/'bootstrap_controller.log').open('xb') as log:
 p=subprocess.Popen([sys.executable,'-u','-B','/content/exp007_bootstrap.py'],stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
print(json.dumps({'pid':p.pid,'root':str(root)}))
