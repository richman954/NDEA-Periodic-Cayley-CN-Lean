"""Bounded offline tests for the full-predecessor Exp015 combined source protocol."""
import ast, datetime, hashlib, importlib.util, json, shutil, tempfile
from pathlib import Path

root = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('exp015_generator_test', root/'make_combined.py')
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
checks = []


def accepted(label, condition):
    if not condition:
        raise RuntimeError(label)
    checks.append(label)


def rejected(label, action):
    try:
        action()
    except RuntimeError:
        checks.append(label)
    else:
        raise RuntimeError('Accepted invalid input: '+label)


for filename in ['make_combined.py', 'verify_combined.py', 'test_combined_infrastructure.py']:
    ast.parse((root/filename).read_text(), filename=filename)
checks.append('infrastructure_python_syntax')
foundation, pins = generator.build_foundation(root)
accepted('exact_full_predecessor_foundation_reconstruction',
         foundation == (root/'lean/Exp014Foundation.lean').read_text())
accepted('full_combined_provenance_matches_sealed_original',
         all((root/path).read_bytes() == (root.parent/'exp014/lean'/Path(path).name).read_bytes()
             for path in pins))
with tempfile.TemporaryDirectory(prefix='exp015_combined_fixture_') as temporary:
    fixture = Path(temporary)
    for directory in ['lean', 'verification_tools', 'predecessor_sources']:
        (fixture/directory).mkdir()
    for relative in list(pins)+['verification_tools/verify_exp005.py',
                                'lean/Exp014Foundation.lean']:
        shutil.copyfile(root/relative, fixture/relative)
    expected = []
    for index, name in enumerate(generator.MODULES):
        text = ('import GenericUniqueness\nnamespace NDEAEvolve.Exp015\n'
                '/- theorem fake_from_comment : False := by contradiction -/\n'
                'private theorem hidden_'+name+' : True := by trivial\n'
                '@[simp] theorem public_'+name+' : True := by trivial\n'
                'end NDEAEvolve.Exp015\n')
        (fixture/'lean'/(name+'.lean')).write_text(text)
        expected.append('NDEAEvolve.Exp015.public_'+name)
    combined, receipt = generator.build(fixture)
    accepted('complete_new_catalog_ignores_comments_and_private_declarations',
             receipt['expected_audits'] == expected)
    accepted('full_predecessor_bodies_retained_without_old_audit_commands',
             'namespace NDEAEvolve.Exp014' in combined and 'namespace NDEAEvolve.Exp013' in combined
             and 'theorem classical_unique' in combined and 'theorem global_classical_exists_unique' in combined
             and '#print axioms NDEAEvolve.Exp014.' not in combined)
    accepted('all_provenance_files_are_in_source_delivery_map',
             all(receipt['source_hashes'].get(name) == digest for name, digest in pins.items())
             and receipt['retained_predecessor_source_hashes'] == pins)
    first = fixture/'predecessor_sources/Exp014Combined.lean'
    original = first.read_bytes()
    first.write_bytes(original+b'\n')
    rejected('changed_sealed_combined_original_rejected', lambda: generator.build(fixture))
    first.write_bytes(original)
    first = fixture/'lean/Exp014Foundation.lean'
    original = first.read_bytes()
    first.write_bytes(original+b'\n')
    rejected('changed_derived_foundation_rejected', lambda: generator.build(fixture))
    first.write_bytes(original)
    control = fixture/'lean/Controls.lean'
    original = control.read_text()
    control.write_text('import Exp012Foundation\n'+original)
    rejected('unembedded_numerical_project_import_rejected', lambda: generator.build(fixture))
    control.write_text(original.replace('public_Controls', 'public_ScalarSqrtEstimate'))
    rejected('duplicate_public_name_rejected', lambda: generator.build(fixture))
    control.write_text(original.replace('namespace NDEAEvolve.Exp015', 'namespace NDEAEvolve.Exp014'))
    rejected('new_public_declaration_outside_exp015_rejected', lambda: generator.build(fixture))
    control.write_text(original)
    control.rename(control.with_suffix('.pending'))
    rejected('missing_control_source_rejected', lambda: generator.build(fixture))

receipt = {'passed': True, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'checks': checks, 'check_count': len(checks),
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'scope': 'Focused offline source reconstruction and rejection fixtures. No Lean invocation, '
                    'network action, final source delivery, or final proof acceptance.'}
(root/'evidence/COMBINED_INFRASTRUCTURE_TESTS.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
