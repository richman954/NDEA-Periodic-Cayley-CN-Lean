import json,subprocess
from pathlib import Path
root=Path('/content/exp008_check')
for name in ['bootstrap/RESULT.json','EXTRA_IMPORTS.json','development/evidence/FOUNDATION_RESULT.json','final_verification/RESULT.json']:
    p=root/name
    if p.is_file():
        d=json.loads(p.read_text())
        print(name,json.dumps({k:d.get(k) for k in ['passed','exit_code','error','elapsed_seconds','start_utc','end_utc','dependency_artifacts']}))
        if d.get('commands'):
            last=d['commands'][-1]
            print('latest bootstrap command',json.dumps({k:last.get(k) for k in ['label','exit_code','elapsed_seconds']}))
for p in sorted((root/'development/batches').glob('*/RESULT.json')):
    d=json.loads(p.read_text())
    print(str(p.relative_to(root)),json.dumps({'passed':d['passed'],'error':d.get('error'),
        'modules':[{k:m.get(k) for k in ['module','exit_code','elapsed_seconds']} for m in d.get('modules',[])]}))
    if d.get('error') and d.get('modules'):
        log=p.parent/(d['modules'][-1]['module']+'.log')
        print(log.read_text()[-2500:])
print(subprocess.run(['pgrep','-af','lean.*Exp00[78]|verify_combined'],text=True,capture_output=True).stdout[-1500:])
