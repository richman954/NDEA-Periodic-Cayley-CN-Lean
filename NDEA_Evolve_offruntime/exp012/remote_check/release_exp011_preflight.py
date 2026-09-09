from pathlib import Path
import hashlib,json,subprocess
root=Path('/content/exp011_check')
expected='a986cfb44931f34d433306697d961ee7407d058f14e9ca9ce5b8010065401a28'
result=json.loads((root/'final_verification/RESULT.json').read_text())
receipt=json.loads((root/'EXPORT_RECEIPT.json').read_text())
archive=Path(receipt['archive'])
assert result['passed'] and result['exit_code']==0
assert receipt['passed'] and receipt['sha256']==expected
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
processes=subprocess.run(['ps','-eo','comm,args'],text=True,capture_output=True,check=True).stdout.splitlines()
active=[line for line in processes if line.split(maxsplit=1)[0] in {'lean','lake'}]
assert not active,active
print(json.dumps({'passed':True,'completed_session':'exp011-independent-check','evidence_archive_sha256':expected,'active_lean_or_lake_processes':active}))
