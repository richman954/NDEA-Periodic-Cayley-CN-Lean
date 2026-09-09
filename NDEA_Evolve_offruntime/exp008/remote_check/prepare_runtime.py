"""Prepare isolated Exp008 development directories on the independent Colab VM."""
import hashlib,json
from pathlib import Path

base=Path('/content/exp008_check')
root=Path('/content/exp008_check')
lean=base/'lean-4.31.0-linux/bin/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sha(lean)!='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':
    raise RuntimeError('Pinned compiler mismatch')
for d in ['development/lean','development/lib','development/evidence','diagnostics']:
    (root/d).mkdir(parents=True,exist_ok=True)
source=root/'inputs/Exp007Foundation.lean'
if sha(source)!='cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c':
    raise RuntimeError('Foundation source mismatch')
(root/'development/lean/Exp007Foundation.lean').write_bytes(source.read_bytes())
receipt={'root':str(root),'compiler':str(lean),'compiler_sha256':sha(lean),
         'external_library':str(base/'mathlib/.lake/build/lib/lean'),
         'scope':'Fresh Exp008 Colab environment independently downloads the pinned compiler/libraries; project sources compile in isolated development directories.'}
(root/'ENVIRONMENT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
