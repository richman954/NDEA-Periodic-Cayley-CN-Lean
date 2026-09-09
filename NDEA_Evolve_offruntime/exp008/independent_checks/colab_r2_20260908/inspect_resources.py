from pathlib import Path
import json,shutil,subprocess
root=Path('/content/exp008_check')
usage=shutil.disk_usage(root)
print(json.dumps({'disk_free_gb':usage.free/1e9,'disk_used_gb':usage.used/1e9}))
p=root/'historical_verification/dependency_copy.log'
if p.is_file():print('dependency_copy.log',p.read_text()[-1800:])
p=root/'historical_verification/DEPENDENCY_ARTIFACTS.json'
print('dependency_manifest_ready',p.is_file())
for line in subprocess.check_output(['ps','-eo','pid,comm,etime,pcpu,rss'],text=True).splitlines():
    words=line.split()
    if len(words)>1 and words[1] in {'lean','python3','python'}:print(line)
