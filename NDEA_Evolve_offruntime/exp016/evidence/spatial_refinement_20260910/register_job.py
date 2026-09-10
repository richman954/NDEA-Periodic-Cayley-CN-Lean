"""Compact mutable job register for the unchanged source-bound Lean runner."""
import importlib.util
import json
from pathlib import Path
import sys

ACTIVE = Path(__file__).resolve().parents[2]
RECOVERY = Path('/home/richman954/NDEA_Recovery')
name, session = sys.argv[1], int(sys.argv[2])
receipt = sorted((ACTIVE / 'evidence').glob('*_' + name + '.json'))[-1]
r = json.loads(receipt.read_text())
spec = importlib.util.spec_from_file_location('checkpoint', RECOVERY / 'checkpoint.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
task = json.loads((RECOVERY / 'TASK_STATE.json').read_text())
assert not any(j.get('session_id') == session for j in task['job_register'])
job = {'purpose': name + ' pinned development check',
    'command': 'python3 -u -B run_lean.py lean/' + name + '.lean',
    'inner_command': r['command'], 'session_id': session,
    'pid': 'not exposed by execution interface', 'cwd': str(ACTIVE),
    'environment': 'local Lean 4.31.0; pinned Mathlib; shared single-job lock',
    'source': r['source'], 'source_sha256': r['source_sha256_before'],
    'runner_sha256': r['runner_sha256'], 'started_utc': r['start_utc'],
    'observed_utc': c.utc(), 'status': 'running; no completed acceptance yet',
    'receipt': str(receipt), 'log': str(receipt.with_suffix('.log'))}
task['job_register'].append(job)
task['recovery']['current_check'] = job.copy()
task['updated_utc'] = c.utc()
c.atomic_bytes(RECOVERY / 'TASK_STATE.json', c.json_bytes(task))
print(json.dumps(job, indent=2))
