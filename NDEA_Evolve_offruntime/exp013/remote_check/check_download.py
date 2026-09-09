"""Validate transferred independent evidence against the accepted local proof."""
import argparse, datetime, hashlib, importlib.util, json, math, re, tarfile, uuid
from pathlib import Path, PurePosixPath

root=Path(__file__).resolve().parent.parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('archive',type=Path)
p.add_argument('--sha256',required=True)
p.add_argument('--extract-to',type=Path,required=True)
a=p.parse_args()
sha=lambda data:hashlib.sha256(data).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)


def validate_fresh_bootstrap(files, root, final_inputs, final_result):
    """Bind the fresh allocation, exact bootstrap inputs, and completed command logs."""
    remote_root = PurePosixPath('/content/exp013_check')
    lean = str(remote_root/'lean-4.31.0-linux/bin/lean')
    environment_path = root/'remote_check/ENVIRONMENT_EXPECTED.json'
    allocation_path = root/'remote_check/VM_ALLOCATION.json'
    bootstrap_inputs_path = root/'remote_check/BOOTSTRAP_INPUTS.json'
    bootstrap_script_path = root/'remote_check/bootstrap.py'
    bootstrap_launcher_path = root/'remote_check/start_bootstrap.py'
    predecessor_environment_path = root/'remote_check/PREDECESSOR_ENVIRONMENT.json'
    accepted_local = {str(p.relative_to(root)) for p in [environment_path,
        allocation_path, bootstrap_inputs_path, bootstrap_script_path, bootstrap_launcher_path,
        predecessor_environment_path]}
    environment_bytes = environment_path.read_bytes()
    require(files['ENVIRONMENT.json'] == environment_bytes, 'Fresh runtime receipt changed')
    environment = json.loads(environment_bytes)
    allocation = json.loads(allocation_path.read_text())
    require(sha(predecessor_environment_path.read_bytes()) ==
        '4bb371158ed752d8f7f0ff2a0cc101187dbc1c50871e87ae8d86df4504c69954',
        'Accepted Experiment 012 environment record changed')
    predecessor_environment = json.loads(predecessor_environment_path.read_text())
    require(environment.get('passed') is True and environment.get('fresh_root') is True
        and environment.get('prior_project_paths') == [] and
        environment.get('root') == str(remote_root), 'Runtime was not recorded as fresh')
    require(environment.get('session') == allocation.get('session') == 'exp013-independent-check-r2'
        and allocation.get('root') == str(remote_root) and
        allocation.get('distinct_allocation') is True, 'Fresh allocation/session mismatch')
    prior_vm_ids = allocation.get('previous_vm_ids')
    require(isinstance(prior_vm_ids, list) and len(prior_vm_ids) == len(set(prior_vm_ids))
        and {'m-s-kkb-usw4c1-1loxz56gsupls','m-s-kkb-usw3b1-3oqo9i5fec2ow','m-s-kkb-use1c1-1e742c6fpiifs','m-s-kkb-usc1a1-d4w1b6hb9jym',
             'm-s-kkb-usc1b1-2yftnii3g1zpd',
             'm-s-kkb-usc1c1-1p1nzzki4492q',
             'm-s-kkb-usc1c0-1k0px308tu45q'} <= set(prior_vm_ids)
        and all(isinstance(v, str) and v for v in prior_vm_ids)
        and isinstance(allocation.get('vm_id'), str) and allocation['vm_id']
        and allocation['vm_id'] not in prior_vm_ids, 'Fresh VM is not distinct from predecessors')
    boot_id = environment.get('boot_id')
    require(isinstance(boot_id, str) and str(uuid.UUID(boot_id)) == boot_id and
        boot_id not in {predecessor_environment['boot_id'],
            '75274d51-536c-4a5f-a2de-f5814d0d098f'}, 'Fresh boot identity did not change')

    expected = json.loads(bootstrap_inputs_path.read_text())
    input_hashes = expected['files']
    require(isinstance(input_hashes, dict) and set(input_hashes) ==
        {'Combined.lean', 'bootstrap_colab.py', 'lake-manifest.json',
         'lean_import_closure.py', 'verify_exp005.py'}, 'Bootstrap input catalog changed')
    require(input_hashes['Combined.lean'] == final_inputs['source_sha256'],
        'Bootstrap dependency roots came from a different combined proof')
    require(input_hashes['lake-manifest.json'] ==
        '8b502ab62ab6af3f90f3d7c43a55f25af4eb0f762da7937414bf3a89df0d3158' and
        input_hashes['bootstrap_colab.py'] ==
        'fc71e6c1453d81e5f9b23d39e45a5ab154ffedb0e3cae3ac36ee6b1bae6d1c67' and
        input_hashes['lean_import_closure.py'] ==
        '12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057' and
        input_hashes['verify_exp005.py'] ==
        'fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb',
        'Frozen bootstrap helper/dependency pins changed')
    input_names = set(input_hashes) | {'INPUT_HASHES.json'}
    require({name.removeprefix('inputs/') for name in files if name.startswith('inputs/')} ==
        input_names, 'Bootstrap input evidence coverage mismatch')
    require(json.loads(files['inputs/INPUT_HASHES.json']) == input_hashes,
        'Bootstrap input hash manifest differs')
    for name in sorted(input_names):
        local_path = root/'remote_check/bootstrap_inputs'/name
        require(files['inputs/'+name] == local_path.read_bytes(),
            'Bootstrap input bytes differ: '+name)
        accepted_local.add(str(local_path.relative_to(root)))
        if name in input_hashes:
            require(sha(files['inputs/'+name]) == input_hashes[name],
                'Bootstrap input hash differs: '+name)

    archive_path = root/'remote_check/bootstrap_inputs.tar.gz'
    require(sha(archive_path.read_bytes()) == expected['archive_sha256'],
        'Local bootstrap delivery archive changed')
    archive_files = {}
    with tarfile.open(archive_path) as tar:
        for item in tar.getmembers():
            require(item.isfile() and item.name in input_names and item.name not in archive_files,
                'Unexpected/duplicate bootstrap delivery member')
            archive_files[item.name] = tar.extractfile(item).read()
    require(set(archive_files) == input_names and all(archive_files[name] == files['inputs/'+name]
        for name in input_names), 'Bootstrap delivery/archive evidence disagrees')
    accepted_local.add(str(archive_path.relative_to(root)))
    bootstrap_script_hash = sha(bootstrap_script_path.read_bytes())
    require(expected['bootstrap_sha256'] == bootstrap_script_hash and
        expected['start_bootstrap_sha256'] == sha(bootstrap_launcher_path.read_bytes()),
        'Pinned bootstrap driver/launcher changed')
    for name,digest in [('EXPECTED_ARCHIVE_SHA256',expected['archive_sha256']),
                        ('EXPECTED_BOOTSTRAP_SHA256',bootstrap_script_hash)]:
        pins_in_launcher=re.findall(rf"^{name} = '([0-9a-f]{{64}})'$",
            bootstrap_launcher_path.read_text(),re.M)
        require(pins_in_launcher==[digest], 'Bootstrap launcher delivery pin differs')
    require(files['bootstrap_tools/bootstrap.py'] == bootstrap_script_path.read_bytes(),
        'Accepted bootstrap script differs from current source')
    launch = json.loads(files['BOOTSTRAP_LAUNCH.json'])
    require(launch['root'] == str(remote_root) and launch['archive_sha256'] == expected['archive_sha256']
        and launch['bootstrap_sha256'] == bootstrap_script_hash and
        launch['input_hashes'] == input_hashes, 'Bootstrap launch pins differ')
    launch_command = launch.get('command')
    require(isinstance(launch_command, list) and len(launch_command) == 4 and
        isinstance(launch_command[0], str) and
        re.fullmatch(r'/usr/(?:local/)?bin/python(?:3(?:\.[0-9]+)?)?', launch_command[0]) is not None
        and launch_command[1:] == ['-u', '-B', '/content/exp013_bootstrap.py'] and
        isinstance(launch.get('pid'), int) and launch['pid'] > 0,
        'Unexpected bootstrap launch command')

    bootstrap = json.loads(files['bootstrap/RESULT.json'])
    pins = json.loads(files['inputs/lake-manifest.json'])['packages']
    require(bootstrap.get('passed') is True and bootstrap.get('error') is None,
        'Independent dependency bootstrap did not complete')
    require(bootstrap['input_hashes'] == input_hashes and
        bootstrap['compiler_sha256'] == final_result['compiler_sha256'] ==
        'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550' and
        bootstrap['dependency_pins'] == final_result['dependency_pins'] == pins,
        'Bootstrap and final proof compiler/dependency/input pins disagree')
    require(re.fullmatch(r'[0-9a-f]{64}', bootstrap.get('archive_sha256', '')) is not None,
        'Downloaded compiler archive hash is absent')
    def utc(value):
        result = datetime.datetime.fromisoformat(value)
        require(result.tzinfo is not None, 'Naive verification timestamp')
        return result.astimezone(datetime.timezone.utc)
    # The allocation receipt uses the local machine's clock. Compare chronology
    # only among receipts produced on this one VM; the two clocks can differ.
    utc(allocation['utc'])
    require(utc(environment['utc']) <= utc(bootstrap['start_utc']) <=
        utc(bootstrap['end_utc']) <= utc(final_result['start_utc']) <= utc(final_result['end_utc']),
        'Fresh initialization/bootstrap/proof timestamps are inconsistent')

    commands = bootstrap.get('commands')
    require(isinstance(commands, list) and len(commands) > 2 + 5*len(pins),
        'Bootstrap command history is incomplete')
    labels = set()
    command_logs = set()
    for index, row in enumerate(commands, 1):
        label = row.get('label')
        require(isinstance(label, str) and re.fullmatch(r'[A-Za-z0-9_]+', label) is not None
            and label not in labels, 'Unsafe/duplicate bootstrap command label')
        labels.add(label)
        log_name = f'bootstrap/{index:03d}_{label}.log'
        require(row.get('log') == str(remote_root/log_name), 'Noncanonical bootstrap command log path')
        require(row.get('exit_code') == 0 and isinstance(row.get('elapsed_seconds'), (int, float)) and
            math.isfinite(row['elapsed_seconds']) and row['elapsed_seconds'] >= 0,
            'Failed/incomplete bootstrap command: '+label)
        require(sha(files[log_name]) == row.get('log_sha256'), 'Bootstrap command log hash differs: '+label)
        require(isinstance(row.get('command'), list) and row['command'] and
            all(isinstance(part, str) for part in row['command']), 'Invalid bootstrap command vector')
        command_logs.add(log_name)
    require({name for name in files if name.startswith('bootstrap/') and name.endswith('.log')} ==
        command_logs, 'Bootstrap command log coverage mismatch')
    expected_commands = [('download_lean', ['curl', '-fL', '--retry', '3', '--connect-timeout', '30',
        '--max-time', '900', 'https://github.com/leanprover/lean4/releases/download/v4.31.0/'
        'lean-4.31.0-linux.tar.zst', '-o', str(remote_root/'lean-4.31.0-linux.tar.zst')])]
    package_roots = []
    for pin in sorted(pins, key=lambda pin: pin['name'] != 'mathlib'):
        target = remote_root/'mathlib' if pin['name'] == 'mathlib' else remote_root/'mathlib/.lake/packages'/pin['name']
        target = str(target)
        package_roots.append(target)
        expected_commands.extend([
            ('init_'+pin['name'], ['git', 'init', '-q', target]),
            ('remote_'+pin['name'], ['git', '-C', target, 'remote', 'add', 'origin', pin['url']]),
            ('fetch_'+pin['name'], ['git', '-C', target, 'fetch', '--depth=1', 'origin', pin['rev']]),
            ('checkout_'+pin['name'], ['git', '-C', target, 'checkout', '-q', '--detach', 'FETCH_HEAD']),
            ('pin_'+pin['name'], ['git', '-C', target, 'rev-parse', 'HEAD'])])
    for row, (label, command) in zip(commands, expected_commands):
        require(row['label'] == label and row['command'] == command, 'Bootstrap download/checkout command differs')
        if label.startswith('pin_'):
            pin = next(pin for pin in pins if label == 'pin_'+pin['name'])
            log_name = str(PurePosixPath(row['log']).relative_to(remote_root))
            require(files[log_name].decode().strip() == pin['rev'], 'Bootstrap git revision output differs')
    cache_modules_built = set()
    for row in commands[len(expected_commands):-1]:
        command = row['command']
        require(len(command) == 8 and command[:3] == [lean, '-j', '1'] and
            command[3] == '-R' and command[4] in package_roots and command[5] == '-o',
            'Unexpected bootstrap cache-client compiler command')
        source_root = PurePosixPath(command[4])
        source_path = PurePosixPath(command[7])
        require(str(source_path) == command[7] and '..' not in source_path.parts and
            source_path.is_relative_to(source_root) and source_path.suffix == '.lean',
            'Unsafe cache-client source path')
        relative = source_path.relative_to(source_root)
        module = str(relative.with_suffix('')).replace('/', '.')
        target = remote_root/'bootstrap/cache_client/lib/lean'/relative.with_suffix('.olean')
        require(command[6] == str(target) and row['label'] == 'cache_'+module.replace('.', '_') and
            module not in cache_modules_built, 'Cache-client source/output/label mismatch')
        cache_modules_built.add(module)
    require('Cache.Main' in cache_modules_built, 'Cache-client entrypoint was not built')
    cache_modules = bootstrap['cache_modules']
    requested_modules = {m for m in final_inputs['external_imports'] if m.startswith('Mathlib.')}
    extra_modules = {'Mathlib.LinearAlgebra.Matrix.Kronecker', 'Mathlib.Analysis.SpecialFunctions.Exponential',
        'Mathlib.Analysis.Calculus.Deriv.Mul', 'Mathlib.Analysis.Normed.Algebra.Exponential'}
    require(isinstance(cache_modules, list) and cache_modules == sorted(set(cache_modules)) and
        requested_modules <= set(cache_modules) <= requested_modules | extra_modules,
        'Library cache request differs from combined proof roots')
    require(commands[-1]['label'] == 'mathlib_cache' and commands[-1]['command'] ==
        [lean, '-j', '1', '--run', str(remote_root/'mathlib/Cache/Main.lean'), 'get', *cache_modules],
        'Library cache download command differs')
    footer = json.loads(files['bootstrap_controller.log'].decode().strip().splitlines()[-1])
    require(footer.get('passed') is True and footer.get('error') is None,
        'Bootstrap controller did not report completion')
    return {'passed': True, 'vm_id': allocation['vm_id'], 'boot_id': boot_id,
        'session': environment['session'], 'fresh_root': True,
        'bootstrap_source_sha256': bootstrap_script_hash,
        'bootstrap_input_archive_sha256': expected['archive_sha256'],
        'bootstrap_input_files_verified': len(input_names), 'commands_verified': len(commands),
        'cache_client_modules_built': len(cache_modules_built), 'dependency_packages': len(pins),
        'compiler_sha256': bootstrap['compiler_sha256'],
        'bootstrap_start_utc': bootstrap['start_utc'], 'bootstrap_end_utc': bootstrap['end_utc']}, accepted_local

require(sha(a.archive.read_bytes())==a.sha256,'Archive checksum mismatch')
files={}
with tarfile.open(a.archive) as tar:
    for item in tar.getmembers():
        path=PurePosixPath(item.name)
        require(item.isfile() and not path.is_absolute() and '..' not in path.parts
            and str(path)==item.name and item.name not in files,'Unsafe archive member')
        files[item.name]=tar.extractfile(item).read()
manifest=json.loads(files['EVIDENCE_SHA256.json'])
require(set(manifest)==set(files)-{'EVIDENCE_SHA256.json'},'Incomplete evidence manifest')
for name,digest in manifest.items():require(sha(files[name])==digest,'Evidence changed: '+name)
inputs=json.loads((root/'evidence/FINAL_INPUTS.json').read_text())
remote=json.loads(files['final_verification/RESULT.json'])
local=json.loads((root/'evidence/local_combined/RESULT.json').read_text())
require(remote.get('passed') is True and local.get('passed') is True
    and remote.get('exit_code')==local.get('exit_code')==0,'Incomplete checks')
transfer=json.loads(files['final_source/FINAL_TRANSFER_INPUTS.json'])
request=json.loads((root/'remote_check/FINAL_UPLOAD.json').read_text())
require(request==json.loads(files['FINAL_UPLOAD.json']),'Remote request mismatch')
require(files['ENVIRONMENT.json']==(root/'remote_check/ENVIRONMENT_EXPECTED.json').read_bytes(),
    'Independent runtime receipt changed')
launch=json.loads(files['FINAL_LAUNCH.json'])
require(launch['combined_sha256']==inputs['source_sha256'] and
    launch['source_archive_sha256']==request['sha256'] and
    launch['runner_sha256']==sha((root/'verify_combined.py').read_bytes()),
    'Independent launch receipt differs')
require(transfer==request['files'],'Transferred source manifest mismatch')
require(set(transfer)=={n.removeprefix('final_source/') for n in files
    if n.startswith('final_source/')} - {'FINAL_TRANSFER_INPUTS.json'},'Source coverage mismatch')
for name,digest in transfer.items():
    require(sha(files['final_source/'+name])==digest==sha((root/name).read_bytes()),
        'Local/remote verification input differs: '+name)
require(inputs==json.loads(files['final_source/evidence/FINAL_INPUTS.json']),
    'Independent source catalog differs')
for result in [local,remote]:
    require(result['runner_sha256']==sha((root/'verify_combined.py').read_bytes()),
        'Accepted verifier differs from current verifier')
    require(result['reconstruction_verified'] is True,'Source reconstruction missing')
    require(result['source_sha256_before']==result['source_sha256_after']==inputs['source_sha256'],
        'Combined source disagreement')
    require(result['source_hashes']==inputs['source_hashes'],'Module hash disagreement')
require(remote['compiler_sha256']==local['compiler_sha256']==
    'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Compiler pin differs')
require(remote['dependency_pins']==local['dependency_pins'],'Library source pins differ')
bootstrap_verification, bootstrap_local_files = validate_fresh_bootstrap(files, root, inputs, remote)
require(remote['command']==['/content/exp013_check/lean-4.31.0-linux/bin/lean','-j','1',
    '/content/exp013_check/final_source/lean/Exp013Combined.lean'],'Unexpected remote command')
require(remote['lean_path']=='/content/exp013_check/final_verification/dependencies:'
    '/content/exp013_check/lean-4.31.0-linux/lib/lean','Unexpected remote import path')
checker=root/'verification_tools/verify_exp005.py'
require(sha(checker.read_bytes())=='fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb',
    'Audit checker pin differs')
spec=importlib.util.spec_from_file_location('audit',checker)
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
expected=set(inputs['expected_audits'])
for result,log in [(remote,files['final_verification/combined.log']),
    (local,(root/'evidence/local_combined/combined.log').read_bytes())]:
    require(sha(log)==result['log_sha256'],'Compiler log changed')
    rows={k:sorted(v) for k,v in audit.validate_axiom_log(log.decode(),expected).items()}
    require(rows==result['axiom_audits'],'Reported audits differ from compiler output')
require(local['axiom_audits']==remote['axiom_audits'],'Cross-environment audit mismatch')
libs=json.loads(files['final_verification/DEPENDENCY_ARTIFACTS.json'])
local_lib_path=root/'evidence/local_combined/DEPENDENCY_ARTIFACTS.json'
local_libs=json.loads(local_lib_path.read_text())
require(sha(files['final_verification/DEPENDENCY_ARTIFACTS.json'])==
    remote['dependency_manifest_sha256'],'Remote library manifest changed')
require(sha(local_lib_path.read_bytes())==local['dependency_manifest_sha256'],
    'Local library manifest changed')
require(libs==local_libs and len(libs)==remote['dependency_artifacts']==local['dependency_artifacts'],
    'Cross-environment library artifact mismatch')
a.extract_to.mkdir(parents=True,exist_ok=False)
for name,data in files.items():
    target=a.extract_to/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
record={'passed':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'archive_sha256':a.sha256,'verified_payload_files':len(manifest),
    'audits_verified':len(expected),'source_sha256':inputs['source_sha256'],
    'dependency_artifacts_agree':len(libs),'local_elapsed_seconds':local['elapsed_seconds'],
    'independent_elapsed_seconds':remote['elapsed_seconds'],
    'checker_sha256':sha(Path(__file__).read_bytes()),
    'bootstrap_verification':bootstrap_verification,
    'accepted_local_files':{name:sha((root/name).read_bytes()) for name in
        sorted(set(transfer)|bootstrap_local_files|{'evidence/local_combined/RESULT.json',
            'evidence/local_combined/combined.log','evidence/local_combined/DEPENDENCY_ARTIFACTS.json',
            'remote_check/FINAL_UPLOAD.json','remote_check/ENVIRONMENT_EXPECTED.json'})},
    'accepted_independent_files':{name:sha(data) for name,data in files.items()},
    'scope':'Fresh-allocation and completed-bootstrap evidence, transfer integrity, exact verification-input agreement, axiom-log validation, and cross-environment artifact comparison. No Lean rerun in this receiving script.'}
(root/'remote_check/FINAL_TRANSFER_CHECK.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
