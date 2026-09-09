from pathlib import Path
import hashlib
import json

root = Path('/content/exp016_dev')
paths = [root, root / 'checks', root / 'checks/20260909T162632.143036Z_ContinuumPotentialStability.zip']
print(json.dumps({'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
    'cwd': str(Path.cwd()), 'paths': [{'path': str(p), 'exists': p.exists(),
      'sha256': hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None}
      for p in paths]}, indent=2))
