import pathlib,tarfile,subprocess,sys,json,hashlib
r=pathlib.Path('/content/exp007_check');source=r/'final_source';source.mkdir(exist_ok=False)
archive=pathlib.Path('/content/exp007_final_sources.tar.gz')
assert hashlib.sha256(archive.read_bytes()).hexdigest()=='6e00d96e9722fa791ff07a4882d54a282cc852345c7db4069ae661395239d71a'
with tarfile.open(archive) as tar:
 for m in tar.getmembers():
  p=pathlib.PurePosixPath(m.name)
  assert m.isfile() and not p.is_absolute() and '..' not in p.parts
 tar.extractall(source,filter='data')
hashes=json.loads((source/'FINAL_TRANSFER_INPUTS.json').read_text())
assert all(hashlib.sha256((source/k).read_bytes()).hexdigest()==v for k,v in hashes.items())
cmd=[sys.executable,'-u','-B',str(source/'verify_combined.py'),'--root',str(source),'--lean',str(r/'lean-4.31.0-linux/bin/lean'),'--mathlib',str(r/'mathlib'),'--other-packages',str(r/'mathlib/.lake/packages'),'--output',str(r/'final_verification')]
with (r/'final_controller.log').open('xb') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,start_new_session=True)
receipt={'pid':p.pid,'command':cmd,'source_archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'runner_sha256':hashlib.sha256((source/'verify_combined.py').read_bytes()).hexdigest()}
(r/'FINAL_LAUNCH.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
