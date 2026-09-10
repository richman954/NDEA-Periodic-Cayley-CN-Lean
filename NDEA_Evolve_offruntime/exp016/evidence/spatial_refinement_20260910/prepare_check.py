"""Record frozen draft identity before the existing manual checkpoint/check."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ACTIVE = Path(__file__).resolve().parents[2]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
name = sys.argv[1]
source = ACTIVE / 'lean' / (name + '.lean')
assert source.is_file()
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
task = json.loads((RECOVERY / 'TASK_STATE.json').read_text())
assert name not in task['accepted_active_modules']
record = {'module': name, 'source': str(source),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'status': 'draft frozen for pinned check; not accepted',
    'command': 'python3 -u -B run_lean.py lean/' + name + '.lean', 'cwd': str(ACTIVE)}
task['recovery']['current_check'] = record
task['draft_sources'] = [str(p.relative_to(ACTIVE)) for p in sorted((ACTIVE / 'lean').glob('*.lean'))
    if p.stem not in task['accepted_active_modules']]
task['updated_utc'] = c.utc()
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(task))
print(json.dumps(record, indent=2))
