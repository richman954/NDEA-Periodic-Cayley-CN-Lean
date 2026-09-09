from pathlib import Path
import json
r=Path('/content/exp007_check/development')
for name in ['FullClosure','StageBridge','Controls']:
 p=r/('integration_r2_'+name+'_RESULT.json')
 if p.exists():
  d=json.loads(p.read_text());print(name,json.dumps(d))
  if d['exit_code']:print((r/('integration_r2_'+name+'.log')).read_text()[-15000:])
print((r/'integration_r2_controller.log').read_text()[-1200:])
