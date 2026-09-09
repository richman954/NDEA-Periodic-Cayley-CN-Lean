import json
from pathlib import Path
import subprocess
root=Path('/content/exp006_check')
for name in ['ADDITIONAL_DEPENDENCIES.json','final_verification/RESULT.json']:
    p=root/name
    if p.is_file():
        d=json.loads(p.read_text())
        print(name,json.dumps({k:v for k,v in d.items() if k not in ['dependency_pins','axiom_audits','expected_audits']}))
for name in ['additional_dependencies.log','final_controller.log','final_verification/combined.log']:
    p=root/name
    if p.is_file(): print(name,p.read_text()[-1600:])
print(subprocess.run(['pgrep','-af','verify_final_exp006|bin/lean'],text=True,capture_output=True).stdout[:1800])
