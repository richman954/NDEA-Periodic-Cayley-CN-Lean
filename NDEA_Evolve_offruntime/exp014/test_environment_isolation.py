"""Exercise the actual checker environment setup with conflicting inherited Lean paths."""
import ast
import datetime
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
checker = root / 'verify_combined.py'
tree = ast.parse(checker.read_text())
selected = []
for node in ast.walk(tree):
    if isinstance(node, ast.Assign) and any(
        isinstance(target, ast.Name) and target.id == 'env' for target in node.targets
    ):
        selected.append(node)
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        function = node.value.func
        if (isinstance(function, ast.Attribute) and isinstance(function.value, ast.Name)
                and function.value.id == 'env' and function.attr == 'pop'):
            selected.append(node)
selected.sort(key=lambda node: node.lineno)


class ConflictingEnvironment:
    environ = {
        'LEAN_PATH': 'untrusted-project-path',
        'LEAN_SRC_PATH': 'untrusted-source-path',
        'LEAN_SYSROOT': 'untrusted-core-path',
        'KEEP': 'yes',
    }


class Arguments:
    lean = Path('/pinned/bin/lean')


namespace = {'os': ConflictingEnvironment, 'library': Path('/isolated/lib'), 'a': Arguments}
module = ast.fix_missing_locations(ast.Module(body=selected, type_ignores=[]))
exec(compile(module, str(checker), 'exec'), namespace)
environment = namespace['env']
checks = {
    'project_path_replaced_and_pinned_core_used':
        environment['LEAN_PATH'] == '/isolated/lib:/pinned/lib/lean',
    'source_path_removed': 'LEAN_SRC_PATH' not in environment,
    'sysroot_override_removed': 'LEAN_SYSROOT' not in environment,
    'unrelated_environment_preserved': environment['KEEP'] == 'yes',
    'single_thread_setting_applied': environment['LEAN_NUM_THREADS'] == '1',
}
if not all(checks.values()):
    raise RuntimeError('Environment isolation failed: ' + repr(checks))
record = {
    'passed': True,
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'checker_sha256': hashlib.sha256(checker.read_bytes()).hexdigest(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'checks': list(checks),
    'scope': 'Executes the actual checker environment-construction AST against deliberately '
             'conflicting inherited Lean variables; no compiler invocation.',
}
(root / 'evidence/ENVIRONMENT_ISOLATION_TEST.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
