"""Initialize a separate experiment on the previously bootstrapped independent VM."""
import datetime, hashlib, json
from pathlib import Path

root = Path('/content/exp009_check')
base = Path('/content/exp008_check')
lean = base / 'lean-4.31.0-linux/bin/lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
if sha(lean) != 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':
    raise RuntimeError('Compiler pin mismatch')
prior = json.loads((base / 'final_verification/RESULT.json').read_text())
if prior.get('passed') is not True:
    raise RuntimeError('Prior independent bootstrap/check is not accepted')
root.mkdir(exist_ok=False)
receipt = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'root': str(root), 'external_base': str(base), 'compiler_sha256': sha(lean),
    'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
    'prior_check_sha256': sha(base / 'final_verification/RESULT.json'),
    'scope': 'Separate Exp009 check on the additional independent Exp008 VM. Reuses its independently downloaded pinned compiler and compatible external libraries. No local project build artifacts are uploaded.'}
(root / 'ENVIRONMENT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
