"""Bounded offline protocol tests; synthetic fixtures are not proof evidence."""
import ast
import copy
import datetime
import hashlib
import importlib.util
import io
import json
import math
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import uuid

root=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
checks=[]
def require(ok,message):
    if not ok:raise RuntimeError(message)
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module
def reject(label,fn):
    try:fn()
    except (RuntimeError,KeyError,ValueError,TypeError):checks.append(label);return
    raise RuntimeError('Incorrectly accepted '+label)
def write_json(path,data):path.write_text(json.dumps(data,indent=2)+'\n')

for path in [root/n for n in ['make_combined.py','verify_combined.py','prepare_final_sources.py',
    'prepare_bootstrap_inputs.py','check_predecessors.py']]+list((root/'remote_check').glob('*.py')):
    ast.parse(path.read_text())
checks.append('infrastructure_python_syntax')

with tempfile.TemporaryDirectory(prefix='exp012_protocol_') as temp:
    fixture=Path(temp)
    for directory in ['lean','evidence','verification_tools','remote_check/bootstrap_inputs']:
        (fixture/directory).mkdir(parents=True,exist_ok=True)
    for name in ['make_combined.py','verify_combined.py','prepare_final_sources.py',
        'prepare_bootstrap_inputs.py','remote_check/start_bootstrap.py','remote_check/bootstrap.py',
        'verification_tools/verify_exp005.py','verification_tools/lean_import_closure.py']:
        shutil.copyfile(root/name,fixture/name)
    for path in (root/'remote_check/bootstrap_inputs').iterdir():
        if path.name not in {'Combined.lean','INPUT_HASHES.json'}:
            shutil.copyfile(path,fixture/'remote_check/bootstrap_inputs'/path.name)
    launcher=fixture/'remote_check/start_bootstrap.py'
    launcher.write_text(re.sub(r"^(EXPECTED_(?:ARCHIVE|BOOTSTRAP)_SHA256) = '[^']+'$",
        r"\1 = 'UNPREPARED'",launcher.read_text(),flags=re.M))
    shutil.copyfile(root/'lean/Exp011Foundation.lean',fixture/'lean/Exp011Foundation.lean')
    modules=['EnergyLocal','EnergyConservation','EnergySeparation','ClassicalUniqueness','Controls']
    for name in modules:
        (fixture/'lean'/(name+'.lean')).write_text(
            'import WeightedTail\nimport Mathlib.Analysis.Calculus.SmoothSeries\n'
            '/-\ntheorem phantom : False := by trivial\n-/\n'
            'noncomputable section\nnamespace NDEAEvolve.Exp012\n'
            f'theorem fixture_{name} : True := by trivial\nend NDEAEvolve.Exp012\n')
    generator=load(fixture/'make_combined.py','exp012_generator_fixture')
    combined,inputs=generator.build(fixture)
    require(len(inputs['expected_audits'])==len(modules) and not any('phantom' in x for x in inputs['expected_audits']),
        'Catalog did not ignore comment text')
    require('Mathlib.Analysis.Calculus.SmoothSeries' in inputs['external_imports'],
        'New derivative import was lost')
    checks += ['complete_fixture_catalog_ignores_comments','smooth_series_import_retained']
    source=fixture/'lean/EnergyLocal.lean';original=source.read_bytes()
    source.write_bytes(original.replace(b'import WeightedTail',b'import UnembeddedProject'))
    reject('unembedded_project_import_rejected',lambda:generator.build(fixture));source.write_bytes(original)
    source.write_bytes(original.replace(b'fixture_EnergyLocal',b'fixture_Controls'))
    reject('duplicate_public_name_rejected',lambda:generator.build(fixture));source.write_bytes(original)
    foundation=fixture/'lean/Exp011Foundation.lean';frozen=foundation.read_bytes()
    foundation.write_bytes(frozen+b'\n')
    reject('changed_foundation_rejected',lambda:generator.build(fixture));foundation.write_bytes(frozen)
    (fixture/'lean/Exp012Combined.lean').write_text(combined)
    write_json(fixture/'evidence/FINAL_INPUTS.json',inputs)
    for name in ['prepare_final_sources.py','prepare_bootstrap_inputs.py']:
        result=subprocess.run([sys.executable,'-B',str(fixture/name)],capture_output=True,text=True)
        require(result.returncode==0,name+' fixture failed: '+result.stderr)
        before={str(p.relative_to(fixture)):sha(p.read_bytes()) for p in fixture.rglob('*') if p.is_file()}
        repeated=subprocess.run([sys.executable,'-B',str(fixture/name)],capture_output=True,text=True)
        after={str(p.relative_to(fixture)):sha(p.read_bytes()) for p in fixture.rglob('*') if p.is_file()}
        require(repeated.returncode!=0 and before==after,'Repeated preparation modified preserved fixture')
        checks.append(name+'_roundtrip_and_repeat_refusal')

    # Transform accepted predecessor bootstrap evidence into an explicit protocol
    # fixture. This exercises the receiver schema, not Experiment 012 mathematics.
    previous=root.parent/'exp011/remote_check/downloaded_evidence'
    files={str(p.relative_to(previous)):p.read_bytes().replace(b'/content/exp011_check',b'/content/exp012_check')
        .replace(b'/content/exp011_bootstrap.py',b'/content/exp012_bootstrap.py')
        for p in previous.rglob('*') if p.is_file()}
    environment=json.loads(files['ENVIRONMENT.json'])
    environment.update(session='exp012-independent-check',boot_id='00000000-0000-4000-8000-000000000012')
    write_json(fixture/'remote_check/ENVIRONMENT_EXPECTED.json',environment)
    files['ENVIRONMENT.json']=(fixture/'remote_check/ENVIRONMENT_EXPECTED.json').read_bytes()
    allocation={'utc':environment['utc'],'root':'/content/exp012_check','session':'exp012-independent-check',
        'vm_id':'SYNTHETIC_EXP012_FIXTURE','distinct_allocation':True,'previous_vm_ids':
        ['m-s-kkb-usw3b1-3oqo9i5fec2ow','m-s-kkb-use1c1-1e742c6fpiifs','m-s-kkb-usc1a1-d4w1b6hb9jym','m-s-kkb-usc1b1-2yftnii3g1zpd','m-s-kkb-usc1c1-1p1nzzki4492q']}
    write_json(fixture/'remote_check/VM_ALLOCATION.json',allocation)
    shutil.copyfile(root/'remote_check/PREDECESSOR_ENVIRONMENT.json',fixture/'remote_check/PREDECESSOR_ENVIRONMENT.json')
    bootstrap_inputs=json.loads((fixture/'remote_check/BOOTSTRAP_INPUTS.json').read_text())
    for path in (fixture/'remote_check/bootstrap_inputs').iterdir():files['inputs/'+path.name]=path.read_bytes()
    files['bootstrap_tools/bootstrap.py']=(fixture/'remote_check/bootstrap.py').read_bytes()
    launch=json.loads(files['BOOTSTRAP_LAUNCH.json'])
    launch.update(archive_sha256=bootstrap_inputs['archive_sha256'],
        bootstrap_sha256=bootstrap_inputs['bootstrap_sha256'],input_hashes=bootstrap_inputs['files'])
    files['BOOTSTRAP_LAUNCH.json']=json.dumps(launch).encode()
    bootstrap=json.loads(files['bootstrap/RESULT.json'])
    bootstrap['input_hashes']=bootstrap_inputs['files']
    bootstrap['cache_modules']=sorted(set(bootstrap['cache_modules'])|{'Mathlib.Analysis.Calculus.SmoothSeries'})
    bootstrap['commands'][-1]['command']=[str(x) for x in bootstrap['commands'][-1]['command'][:6]]+bootstrap['cache_modules']
    for row in bootstrap['commands']:
        key=str(PurePosixPath(row['log']).relative_to('/content/exp012_check'))
        row['log_sha256']=sha(files[key])
    files['bootstrap/RESULT.json']=json.dumps(bootstrap).encode()
    final_result=json.loads(files['final_verification/RESULT.json'])
    tree=ast.parse((root/'remote_check/check_download.py').read_text())
    node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='validate_fresh_bootstrap')
    namespace=dict(globals())
    exec(compile(ast.Module(body=[node],type_ignores=[]),'<bootstrap protocol fixture>','exec'),namespace)
    validate=namespace['validate_fresh_bootstrap']
    result,accepted=validate(files,fixture,inputs,final_result)
    require(result['passed'] and result['commands_verified']==57,'Transformed bootstrap fixture was rejected')
    checks.append('fresh_bootstrap_protocol_fixture_accepted')
    def mutation(label,key,change):
        modified=dict(files);value=json.loads(modified[key]);change(value)
        modified[key]=json.dumps(value).encode()
        reject(label,lambda:validate(modified,fixture,inputs,final_result))
    mutation('failed_bootstrap_rejected','bootstrap/RESULT.json',lambda x:x.update(passed=False))
    mutation('failed_command_rejected','bootstrap/RESULT.json',lambda x:x['commands'][0].update(exit_code=1))
    mutation('wrong_cache_target_rejected','bootstrap/RESULT.json',
        lambda x:x['commands'][46]['command'].__setitem__(6,'/tmp/foreign.olean'))
    mutation('incomplete_cache_roots_rejected','bootstrap/RESULT.json',
        lambda x:x['cache_modules'].remove('Mathlib.Analysis.Calculus.SmoothSeries'))
    modified=dict(files);modified['bootstrap/001_download_lean.log']+=b'changed'
    reject('changed_command_log_rejected',lambda:validate(modified,fixture,inputs,final_result))
    modified=dict(files);del modified['bootstrap/006_pin_mathlib.log']
    reject('missing_command_log_rejected',lambda:validate(modified,fixture,inputs,final_result))
    allocation['vm_id']=allocation['previous_vm_ids'][0]
    write_json(fixture/'remote_check/VM_ALLOCATION.json',allocation)
    reject('reused_vm_identity_rejected',lambda:validate(files,fixture,inputs,final_result))

record={'passed':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'checks':checks,'check_count':len(checks),'script_sha256':sha(Path(__file__).read_bytes()),
    'scope':'Bounded offline infrastructure exercises with synthetic and transformed predecessor fixtures. No Experiment 012 Lean proof or network action is performed or accepted by these tests.'}
(root/'evidence/INFRASTRUCTURE_TESTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
