"""Read the separate Experiment 011 combined-check status."""
import json
from pathlib import Path
root = Path('/content/exp011_check')
bootstrap=root/'bootstrap/RESULT.json'
if bootstrap.is_file():
    d=json.loads(bootstrap.read_text())
    print('bootstrap',json.dumps({k:d.get(k) for k in ['passed','error','start_utc','end_utc']}))
    print('bootstrap_commands',len(d.get('commands',[])),d.get('commands',[])[-1:])
result = root / 'final_verification/RESULT.json'
if result.is_file():
    data = json.loads(result.read_text())
    print(json.dumps({k: data.get(k) for k in ['passed', 'exit_code', 'error',
        'start_utc', 'end_utc', 'elapsed_seconds', 'dependency_artifacts']}))
for name in ['final_controller.log', 'final_verification/combined.log']:
    p = root / name
    if p.is_file():
        print(name, p.read_text()[-1800:])
