"""Record a fresh runtime before any project source or artifact is installed."""
from pathlib import Path
import datetime,json,os,platform

root=Path('/content/exp008_check')
if root.exists():raise RuntimeError('Recheck root already exists; this launch is not fresh')
prior=[str(p) for pattern in ['exp00*_check','exp00*_independent_check','NDEA*']
       for p in Path('/content').glob(pattern)]
if prior:raise RuntimeError('Existing project runtime paths: '+str(prior))
root.mkdir()
record={'passed':True,'fresh_root':True,'prior_project_paths':prior,
        'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'session':'exp008-fresh-recheck-r2','platform':platform.platform(),
        'python':platform.python_version(),'logical_cpus':os.cpu_count(),
        'boot_id':Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
        'scope':'New Colab allocation; project root absent before initialization. No project build artifacts uploaded.'}
(root/'FRESH_VM.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
