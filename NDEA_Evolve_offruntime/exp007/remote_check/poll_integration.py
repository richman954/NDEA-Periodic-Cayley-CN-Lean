from pathlib import Path
import json
r=Path('/content/exp007_check/development')
for name in ['SpinorGrid','ContinuumSpinor','FullClosure','StageBridge','Controls']:
 p=r/('integration_'+name+'_RESULT.json')
 if p.exists():
  d=json.loads(p.read_text());print(name,json.dumps(d))
  if d['exit_code']:print((r/('integration_'+name+'.log')).read_text()[-15000:])
print((r/'integration_controller.log').read_text()[-1200:])
