"""Compact status for this additional independent source recheck."""
from pathlib import Path
import json
root=Path('/content/exp008_check')
for name in ['bootstrap/RESULT.json','EXTRA_IMPORTS.json','final_verification/RESULT.json',
             'historical_verification/RESULT.json']:
    p=root/name
    if not p.is_file():continue
    d=json.loads(p.read_text())
    summary={k:d.get(k) for k in ['passed','start_utc','end_utc','exit_code','error',
             'elapsed_seconds','dependency_artifacts']}
    if 'commands' in d:
        summary['completed_commands']=sum('exit_code' in row for row in d['commands'])
        summary['latest_command']=d['commands'][-1] if d['commands'] else None
    if 'checks' in d:summary['checks']=d['checks']
    print(name,json.dumps(summary))
for name in ['bootstrap_controller.log','extra_imports_controller.log','final_controller.log',
             'final_verification/combined.log','historical_controller.log']:
    p=root/name
    if p.is_file():print(name,p.read_text()[-1400:])
