"""Record the fresh Experiment 010 Colab allocation before installing proof inputs."""
import datetime, json, os, platform
from pathlib import Path
root=Path('/content/exp010_check')
prior=[str(p) for pattern in ['exp0*_check','exp0*_independent_check','NDEA*']
    for p in Path('/content').glob(pattern)]
if root.exists() or prior:raise RuntimeError('Project paths already exist: '+str(prior))
root.mkdir()
record={'passed':True,'fresh_root':True,'prior_project_paths':prior,
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'session':'exp010-independent-check','root':str(root),'platform':platform.platform(),
    'python':platform.python_version(),'logical_cpus':os.cpu_count(),
    'boot_id':Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
    'scope':'New Experiment 010 Colab allocation. Project runtime paths absent before initialization. Pinned compiler and external libraries will be independently downloaded; no project artifacts uploaded.'}
(root/'ENVIRONMENT.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
