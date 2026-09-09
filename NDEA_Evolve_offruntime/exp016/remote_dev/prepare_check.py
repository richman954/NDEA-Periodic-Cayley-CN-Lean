"""Prepare a source-bound Colab command file; this does not run a compiler."""
from pathlib import Path
import base64, hashlib, json, sys

root = Path(__file__).resolve().parent
module = sys.argv[1]
assert module.isidentifier()
source = root.parent / 'lean' / (module + '.lean')
files = {'project/exp016/lean/' + source.name: source.read_bytes(),
         'run_module.py': (root/'run_module.py').read_bytes()}
encoded = {k: base64.b64encode(v).decode() for k,v in files.items()}
script = """from pathlib import Path
import base64, subprocess, sys
r=Path('/content/exp016_dev')
for name, data in FILES.items():
 p=r/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(data))
result=subprocess.run([sys.executable,'-u',str(r/'run_module.py'),MODULE],capture_output=True,text=True)
print(result.stdout,flush=True)
print(result.stderr,flush=True)
print('RUNNER_EXIT_STATUS',result.returncode,flush=True)
""".replace('FILES', repr(encoded)).replace('MODULE', repr(module))
target = root / ('check_' + module + '.py')
target.write_text(script)
print(json.dumps({'command_file': str(target), 'module': module,
                  'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}))
