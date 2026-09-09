"""Validate remote development evidence and install a matching local artifact."""
from pathlib import Path
import datetime, hashlib, json, sys, zipfile

root = Path(__file__).resolve().parent.parent
archive = Path(sys.argv[1]).resolve()
expected = sys.argv[2]
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(archive.read_bytes()) == expected, 'Result archive hash mismatch'
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    rec = json.loads(z.read('RESULT.json'))
    name = rec['module']
    assert name.isidentifier()
    names = {name+'.lean', name+'.olean', 'RESULT.json', 'compiler.log', 'run_module.py'}
    assert set(z.namelist()) == names and len(z.namelist()) == len(names)
    assert rec['exit_code'] == 0 and rec['sources_unchanged'] and rec['imports_unchanged']
    assert rec['independent_qualification'] is False
    source = root / 'lean' / (name+'.lean')
    assert source.read_bytes() == z.read(source.name), 'Current source differs from checked source'
    assert sha(source.read_bytes()) == rec['source_sha256_before'] == rec['source_sha256_after']
    assert sha(z.read('compiler.log')) == rec['log_sha256']
    assert sha(z.read('run_module.py')) == rec['runner_sha256']
    assert sha(z.read(name+'.olean')) == rec['output_sha256']
    assert 'sorryAx' not in z.read('compiler.log').decode()
    stamp = rec['start_utc'].replace(':','').replace('+','_')
    target = root / 'evidence/remote_development' / (stamp+'_'+name)
    target.mkdir(parents=True, exist_ok=False)
    for n in names: (target/n).write_bytes(z.read(n))
    artifact = root / 'build/lib/lean' / (name+'.olean')
    artifact.write_bytes(z.read(name+'.olean'))
    result = {'passed': True, 'module': name, 'archive_sha256': expected,
              'source_sha256': sha(source.read_bytes()), 'receipt': str(target/'RESULT.json'),
              'receipt_sha256': sha(z.read('RESULT.json')), 'log': str(target/'compiler.log'),
              'artifact': str(artifact), 'artifact_sha256': sha(artifact.read_bytes()),
              'independent_qualification': False,
              'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (target/'TRANSFER_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
