"""Pin the exact final source and fresh-VM bootstrap delivery without network calls."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import tarfile

root = Path(__file__).resolve().parent
remote = root/'remote_check'
directory = remote/'bootstrap_inputs'
archive = remote/'bootstrap_inputs.tar.gz'
receipt = remote/'BOOTSTRAP_INPUTS.json'
launcher = remote/'start_bootstrap.py'
sha = lambda data: hashlib.sha256(data).hexdigest()
def require(ok, message):
    if not ok:
        raise RuntimeError(message)

require(not archive.exists() and not receipt.exists(),
        'Bootstrap delivery already exists; preserve its archive and receipt')
launcher_text = launcher.read_text()
for key in ['EXPECTED_ARCHIVE_SHA256', 'EXPECTED_BOOTSTRAP_SHA256']:
    require(f"{key} = 'UNPREPARED'" in launcher_text, 'Bootstrap launcher already pinned')
inputs = json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
spec = importlib.util.spec_from_file_location('exp010_bootstrap_generator', root/'make_combined.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
combined, regenerated = generator.build(root)
require(regenerated == inputs and combined == (root/'lean/Exp010Combined.lean').read_text(),
        'Final combined source/catalog changed before bootstrap preparation')
helper_pins = {
    'bootstrap_colab.py': 'fc71e6c1453d81e5f9b23d39e45a5ab154ffedb0e3cae3ac36ee6b1bae6d1c67',
    'lake-manifest.json': '8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158',
    'lean_import_closure.py': '12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057',
    'verify_exp005.py': 'fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb'}
payload = {name: (directory/name).read_bytes() for name in helper_pins}
require(all(sha(payload[name]) == digest for name, digest in helper_pins.items()),
        'Frozen bootstrap helper or dependency lock changed')
payload['Combined.lean'] = combined.encode()
hashes = {name: sha(data) for name, data in sorted(payload.items())}
payload['INPUT_HASHES.json'] = (json.dumps(hashes, indent=2)+'\n').encode()
for name in ['Combined.lean', 'INPUT_HASHES.json']:
    require(not (directory/name).exists(), 'Bootstrap input already exists: '+name)
    (directory/name).write_bytes(payload[name])
with tarfile.open(archive, 'x:gz') as tar:
    for name, data in sorted(payload.items()):
        member = tarfile.TarInfo(name)
        member.size = len(data)
        member.mode = 0o644
        tar.addfile(member, io.BytesIO(data))
with tarfile.open(archive) as tar:
    members = tar.getmembers()
    require(len(members) == len(payload) and {m.name for m in members} == set(payload),
            'Bootstrap archive member coverage differs')
    for member in members:
        require(member.isfile() and tar.extractfile(member).read() == payload[member.name],
                'Bootstrap archive readback differs')
archive_hash = sha(archive.read_bytes())
bootstrap_hash = sha((remote/'bootstrap.py').read_bytes())
for key, value in [('EXPECTED_ARCHIVE_SHA256', archive_hash),
                   ('EXPECTED_BOOTSTRAP_SHA256', bootstrap_hash)]:
    launcher_text, count = re.subn(rf"^{key} = 'UNPREPARED'$", f"{key} = '{value}'",
                                  launcher_text, flags=re.M)
    require(count == 1, 'Bootstrap launcher pin substitution failed')
launcher.write_text(launcher_text)
record = {'archive': str(archive), 'archive_sha256': archive_hash,
          'bootstrap_sha256': bootstrap_hash, 'start_bootstrap_sha256': sha(launcher.read_bytes()),
          'files': hashes, 'payload_files': len(payload),
          'qualification': 'Exact final-source dependency roots and pinned helpers for a fresh Experiment 010 CPU VM. No network call or compiled project artifact in this preparation.'}
receipt.write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record))
