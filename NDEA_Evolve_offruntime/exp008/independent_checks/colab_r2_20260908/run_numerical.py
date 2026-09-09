"""Rerun the unchanged Exp008 floating-point diagnostics on this fresh VM."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
root=Path('/content/exp008_check/final_verification')
source=root/'numerical_checks.py';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(root/'evidence').mkdir(exist_ok=False)
before=sha(source);begin=time.monotonic();command=[sys.executable,'-B',str(source)]
with (root/'numerical.log').open('xb') as log:
    process=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=120)
data=root/'evidence/numerical_checks.json'
passed=process.returncode==0 and data.is_file() and json.loads(data.read_text()).get('passed') is True
record={'passed':passed,'exit_code':process.returncode,'command':command,
        'source_sha256_before':before,'source_sha256_after':sha(source),
        'log_sha256':sha(root/'numerical.log'),'data_sha256':sha(data) if data.is_file() else None,
        'elapsed_seconds':time.monotonic()-begin,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
if before!=record['source_sha256_after']:record['passed']=False
(root/'NUMERICAL_RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
