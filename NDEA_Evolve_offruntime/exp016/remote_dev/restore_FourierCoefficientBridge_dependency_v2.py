"""Restore one pinned cached Mathlib import closure; never build NDEA or upgrade pins."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, subprocess, time, traceback, zipfile

root = Path('/content/exp016_dev')
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out = root / 'dependency_restores' / (stamp + '_FourierCoefficientBridge')
out.mkdir(parents=True, exist_ok=False)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rec = {'purpose': 'restore pinned cached AddCircle dependency closure',
       'independent_qualification': False, 'passed': False, 'start_utc': stamp}
log = out / 'cache.log'
lean = root / 'lean-4.31.0-linux/bin/lean'
mathlib = root / 'mathlib'
manifest = root / 'inputs/lake-manifest.json'
pins = json.loads(manifest.read_text())['packages']
paths = [mathlib if p['name'] == 'mathlib' else mathlib / '.lake/packages' / p['name']
         for p in pins]

def revision(p):
    return subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'], text=True).strip()

def project_hashes():
    project = root / 'project'
    files = list(project.glob('exp*/lean/*.lean')) + list(project.glob('exp*/build/lib/lean/*.olean'))
    return {str(p.relative_to(project)): sha(p) for p in sorted(files)}

try:
    assert json.loads((root / 'bootstrap/RESULT.json').read_text())['passed']
    assert sha(lean) == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
    assert revision(mathlib) == 'fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
    with (root / 'check.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        rec['compiler_sha256'] = sha(lean)
        rec['bootstrap_receipt_sha256'] = sha(root / 'bootstrap/RESULT.json')
        rec['input_manifest_sha256'] = sha(manifest)
        rec['source_manifest_sha256_before'] = sha(mathlib / 'lake-manifest.json')
        rec['dependency_pins_before'] = {p['name']: revision(q) for p, q in zip(pins, paths)}
        assert all(rec['dependency_pins_before'][p['name']] == p['rev'] for p in pins)
        rec['project_before'] = project_hashes()
        rec['existing_mathlib_olean_paths'] = sorted(str(p.relative_to(mathlib))
                                                   for p in mathlib.rglob('*.olean'))
        env = dict(os.environ, LEAN_NUM_THREADS='1', GIT_TERMINAL_PROMPT='0')
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
            env.pop(key, None)
        env['PATH'] = str(lean.parent) + ':' + env['PATH']
        env['LEAN_PATH'] = str(root / 'bootstrap/cache_client/lib/lean') + ':' + str(lean.parent.parent / 'lib/lean')
        env['LEAN_SRC_PATH'] = ':'.join(map(str, paths))
        command = [str(lean), '-j', '1', '--run', str(mathlib / 'Cache/Main.lean'),
                   'get', 'Mathlib.Analysis.Fourier.AddCircle']
        rec['command'] = command
        print('PINNED CACHE RESTORE RUNNING', str(log), flush=True)
        begin = time.monotonic()
        with log.open('xb') as stream:
            run = subprocess.run(command, cwd=mathlib, env=env, stdout=stream,
                                 stderr=subprocess.STDOUT, timeout=600)
        rec['exit_code'] = run.returncode
        rec['elapsed_seconds'] = time.monotonic() - begin
        rec['dependency_pins_after'] = {p['name']: revision(q) for p, q in zip(pins, paths)}
        rec['pins_unchanged'] = rec['dependency_pins_after'] == rec['dependency_pins_before']
        rec['source_manifest_sha256_after'] = sha(mathlib / 'lake-manifest.json')
        rec['manifest_unchanged'] = rec['source_manifest_sha256_before'] == rec['source_manifest_sha256_after']
        rec['project_unchanged'] = project_hashes() == rec['project_before']
        current = {str(p.relative_to(mathlib)): sha(p) for p in mathlib.rglob('*.olean')
                   if str(p.relative_to(mathlib)) not in rec['existing_mathlib_olean_paths']}
        rec['new_mathlib_olean_sha256'] = current
        rec['restored_addcircle_sha256'] = sha(mathlib / '.lake/build/lib/lean/Mathlib/Analysis/Fourier/AddCircle.olean')
        rec['expected_local_addcircle_sha256'] = 'a761463c2031389bcc8b6337af146ee284f72cdf1724a6ee22febae515dd8cc1'
        assert run.returncode == 0
        assert rec['pins_unchanged'] and rec['manifest_unchanged'] and rec['project_unchanged']
        assert rec['restored_addcircle_sha256'] == rec['expected_local_addcircle_sha256']
        rec['passed'] = True
except Exception as exc:
    rec['error'] = repr(exc)
    traceback.print_exc()
finally:
    rec['end_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    if log.exists():
        rec['log_sha256'] = sha(log)
        print(log.read_text(), flush=True)
    (out / 'RESULT.json').write_text(json.dumps(rec, indent=2) + '\n')
    archive = Path(str(out) + '.zip')
    with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED) as z:
        for p in out.iterdir():
            z.write(p, p.name)
    print(json.dumps({k: rec.get(k) for k in ['passed', 'exit_code', 'elapsed_seconds',
          'pins_unchanged', 'manifest_unchanged', 'project_unchanged', 'restored_addcircle_sha256', 'error']}), flush=True)
    print('RESULT_ARCHIVE', str(archive), 'SHA256', sha(archive), flush=True)
