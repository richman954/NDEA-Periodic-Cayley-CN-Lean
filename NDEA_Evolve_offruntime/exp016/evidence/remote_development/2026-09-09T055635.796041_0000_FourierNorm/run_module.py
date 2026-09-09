"""Pinned incremental development check. Uploaded artifacts preclude qualification."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, resource, subprocess, sys, time, zipfile

root = Path('/content/exp016_dev')
project = root / 'project'
name = sys.argv[1]
assert name.isidentifier(), 'Simple module name required'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
lean = root / 'lean-4.31.0-linux/bin/lean'
assert sha(lean) == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
bootstrap = root / 'bootstrap/RESULT.json'
assert json.loads(bootstrap.read_text())['passed'], 'Dependency bootstrap incomplete'
source = project / 'exp016/lean' / (name + '.lean')
target = project / 'exp016/build/lib/lean' / (name + '.olean')
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out = root / 'checks' / (stamp + '_' + name)
out.mkdir(parents=True)
log = out / 'compiler.log'
receipt = out / 'RESULT.json'
rec = {'purpose': 'incremental development check with imported local artifacts',
       'independent_qualification': False, 'source': str(source),
       'source_sha256_before': sha(source), 'lean_binary_sha256': sha(lean),
       'runner_sha256': sha(Path(__file__)), 'bootstrap_receipt_sha256': sha(bootstrap),
       'start_utc': now(), 'module': name}
save = lambda: receipt.write_text(json.dumps(rec, indent=2) + '\n')
save()
with (root / 'check.lock').open('a') as lock:
    queued = time.monotonic()
    fcntl.flock(lock, fcntl.LOCK_EX)
    rec['lock_wait_seconds'] = time.monotonic() - queued
    rec['compiler_started_utc'] = now()
    rec['project_import_artifacts'] = {
        str(p.relative_to(project)): sha(p)
        for p in sorted(project.glob('exp*/build/lib/lean/*.olean')) if p != target}
    rec['project_sources'] = {
        str(p.relative_to(project)): sha(p) for p in sorted(project.glob('exp*/lean/*.lean'))}
    paths = [project / f'exp{i:03}/build/lib/lean' for i in range(16, 7, -1)]
    paths += [root / 'mathlib/.lake/build/lib/lean']
    paths += [p / '.lake/build/lib/lean' for p in (root / 'mathlib/.lake/packages').iterdir()]
    paths += [project / 'exp006/build/lib/lean', lean.parent.parent / 'lib/lean']
    env = dict(os.environ, LEAN_PATH=':'.join(map(str, paths)), LEAN_NUM_THREADS='1')
    for key in ['LEAN_SRC_PATH', 'LEAN_SYSROOT']: env.pop(key, None)
    rec['lean_path'] = env['LEAN_PATH']
    rec['command'] = [str(lean), '-j', '1', '-R', str(source.parent), '-o', str(target), str(source)]
    save()
    print('COMPILER RUNNING', name, 'SOURCE', rec['source_sha256_before'], 'LOG', log, flush=True)
    start = time.monotonic()
    try:
        with log.open('wb') as stream:
            run = subprocess.run(rec['command'], env=env, cwd=source.parent,
                                 stdout=stream, stderr=subprocess.STDOUT, timeout=600)
        rec['exit_code'] = run.returncode
    except subprocess.TimeoutExpired:
        rec['exit_code'] = 124
    rec.update(elapsed_seconds=time.monotonic()-start, end_utc=now(),
               source_sha256_after=sha(source), log_sha256=sha(log))
    rec['sources_unchanged'] = rec['source_sha256_before'] == rec['source_sha256_after']
    rec['imports_unchanged'] = all(sha(project/p) == h for p, h in rec['project_import_artifacts'].items())
    rec['output_sha256'] = sha(target) if rec['exit_code'] == 0 else None
    save()
    with zipfile.ZipFile(out.with_suffix('.zip'), 'x', zipfile.ZIP_DEFLATED) as z:
        for p in [source, log, receipt, Path(__file__)]: z.write(p, p.name)
        if rec['exit_code'] == 0: z.write(target, target.name)
    print(log.read_text(errors='replace'), flush=True)
    print(json.dumps({k: rec[k] for k in ['module', 'exit_code', 'elapsed_seconds',
        'sources_unchanged', 'imports_unchanged', 'output_sha256', 'independent_qualification']}), flush=True)
    print('RESULT_ARCHIVE', out.with_suffix('.zip'), 'SHA256', sha(out.with_suffix('.zip')), flush=True)
sys.exit(rec['exit_code'])
