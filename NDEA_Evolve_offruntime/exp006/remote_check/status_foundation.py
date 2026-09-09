from pathlib import Path
import subprocess
root=Path('/content/exp006_check')
for name in ['FOUNDATION_RESULT.json','FOUNDATION_DELIVERY.json','foundation.log','foundation_controller.log']:
    p=root/name
    if p.is_file(): print(name,p.read_text()[-3500:])
print(subprocess.run(['pgrep','-af','compile_foundation|bin/lean'],text=True,capture_output=True).stdout[:1800])
