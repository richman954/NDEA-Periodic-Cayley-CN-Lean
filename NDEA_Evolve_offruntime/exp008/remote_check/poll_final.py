"""Report the latest controls attempt and independent combined check."""
from pathlib import Path
import json

root=Path('/content/exp008_check')
for name in ['development/batches/controls_v3/RESULT.json','final_verification/RESULT.json']:
    p=root/name
    if p.is_file():
        d=json.loads(p.read_text())
        print(name,json.dumps({k:d.get(k) for k in
            ['passed','start_utc','end_utc','exit_code','error','elapsed_seconds','dependency_artifacts']}))
for name in ['final_controller.log','final_verification/combined.log']:
    p=root/name
    if p.is_file():print(name,p.read_text()[-1600:])
