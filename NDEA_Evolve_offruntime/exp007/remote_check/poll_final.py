from pathlib import Path
import json
r=Path('/content/exp007_check');p=r/'final_verification/RESULT.json'
if p.exists():
 d=json.loads(p.read_text());print(json.dumps({k:d.get(k) for k in ['passed','exit_code','error','start_utc','end_utc','elapsed_seconds','dependency_artifacts','reconstruction_verified']}))
print((r/'final_controller.log').read_text()[-2000:])
p=r/'final_verification/combined.log'
if p.exists():print(p.read_text()[-2000:])

import subprocess
print(subprocess.run(['pgrep','-af','lean.*Exp007Combined'],text=True,capture_output=True).stdout)
