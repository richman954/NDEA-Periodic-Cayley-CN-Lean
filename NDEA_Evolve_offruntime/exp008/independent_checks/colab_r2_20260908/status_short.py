from pathlib import Path
import json
root=Path('/content/exp008_check')
for name in ['bootstrap/RESULT.json','final_verification/RESULT.json','historical_verification/RESULT.json']:
    p=root/name
    if not p.is_file():continue
    d=json.loads(p.read_text())
    summary={k:d.get(k) for k in ['passed','start_utc','end_utc','exit_code','error','elapsed_seconds','dependency_artifacts']}
    if 'checks' in d:
        summary['checks']=[{k:c.get(k) for k in ['name','passed','exit_code','elapsed_seconds']} for c in d['checks']]
    print(name,json.dumps(summary))
    if 'checks' in d and d['checks'] and not d.get('passed'):
        log=root/'historical_verification'/(d['checks'][-1]['name']+'.log')
        if log.is_file():print('active_check_log_tail',log.read_text()[-1200:])
for name in ['final_controller.log','historical_controller.log']:
    p=root/name
    if p.is_file() and p.stat().st_size:print(name,p.read_text()[-1600:])
