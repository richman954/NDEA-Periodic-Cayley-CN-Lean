"""Read the sealed combined source and inventory public theorem/lemma commands.

This is a source-specific inventory, not a general Lean parser. It removes nested
comments and strings with the sealed portable checker's lexer, tracks namespace
and section commands independently, and rejects unrecognized theorem/lemma lines.
The resulting proposed names still require confirmation by Lean's axiom printer.
It never edits any production source or previously sealed evidence.
"""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
PROJECT = ROOT.parent
SOURCE = ROOT / 'lean/Exp008Combined.lean'
EXPECTED_SHA = '5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


spec = importlib.util.spec_from_file_location(
    'sealed_audit_lexer', ROOT / 'verification_tools/verify_exp005.py')
lexer = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lexer
spec.loader.exec_module(lexer)

# All command shapes used by this particular source must be recognized. A future
# novel shape fails closed instead of silently omitting a public declaration.
DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?P<modifiers>(?:(?:private|protected|noncomputable)\s+)*)'
    r'(?P<kind>theorem|lemma)\s+(?P<name>[^\s(:]+)')
OPEN = re.compile(r'^\s*(?:(noncomputable)\s+)?(namespace|section)(?:\s+(\S+))?\s*$')
END = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
MARKER = re.compile(r'^-- (SOURCE|BEGIN) (.+) SHA256 ([0-9a-f]{64})$')


def declarations(text):
    stack, rows = [], []
    clean = lexer.code_only(text)
    for lineno, line in enumerate(clean.splitlines(), 1):
        if match := OPEN.match(line):
            noncomputable, kind, name = match.groups()
            require(kind != 'namespace' or name is not None,
                    f'Unnamed namespace at {lineno}')
            stack.append({'kind': kind, 'name': name, 'line': lineno})
        elif match := END.match(line):
            require(stack, f'Unmatched end at {lineno}')
            frame = stack.pop()
            require(match[1] is None or match[1] == frame['name'],
                    f'Named end mismatch at {lineno}: {frame}')
        if match := DECL.match(line):
            parts = [frame['name'] for frame in stack if frame['kind'] == 'namespace']
            name = match['name']
            qualified = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(parts + [name])
            rows.append({'name': qualified, 'local_name': name,
                         'line': lineno, 'kind': match['kind'],
                         'private': 'private' in match['modifiers'].split(),
                         'namespace_frames': parts,
                         'named_sections': [frame['name'] for frame in stack
                                            if frame['kind'] == 'section' and frame['name']]})
        elif re.search(r'\b(?:theorem|lemma)\b', line):
            raise RuntimeError(f'Unrecognized declaration-shaped line {lineno}: {line}')
    require(all(frame['kind'] == 'section' and frame['name'] is None for frame in stack),
            f'Unclosed namespace or named section: {stack}')
    require(len(rows) == len({row['name'] for row in rows}), 'Duplicate declaration name')
    return rows, stack


def resolve_marker(path, digest):
    name = Path(path)
    candidates = [name] if name.is_absolute() else [
        ROOT / name, PROJECT / 'exp007' / name,
        PROJECT / 'exp006' / name,
        PROJECT / 'exp006/lean' / name.name,
    ]
    matches = [candidate.resolve() for candidate in candidates
               if candidate.is_file() and sha(candidate) == digest]
    require(bool(matches), f'No current source matches marker: {path} {digest}')
    return matches[0]


def main():
    require(sha(SOURCE) == EXPECTED_SHA, 'Sealed combined source hash mismatch')
    original = SOURCE.read_text()
    lexer.scan_proof_policy(original)
    rows, anonymous_sections = declarations(original)
    markers = []
    for lineno, line in enumerate(original.splitlines(), 1):
        if match := MARKER.match(line):
            kind, path, digest = match.groups()
            resolved = resolve_marker(path, digest)
            markers.append({'marker_kind': kind, 'marker_path': path,
                            'marker_line': lineno, 'source_sha256': digest,
                            'resolved_source': str(resolved)})
    public, private = [], []
    source_cache = {}
    for row in rows:
        marker = max((marker for marker in markers if marker['marker_line'] < row['line']),
                     key=lambda marker: marker['marker_line'])
        path = marker['resolved_source']
        if path not in source_cache:
            source_cache[path] = {entry['name']: entry for entry in declarations(Path(path).read_text())[0]}
        require(row['name'] in source_cache[path], f'Declaration missing in original: {row}')
        original_row = source_cache[path][row['name']]
        require(original_row['private'] == row['private'], f'Visibility differs: {row}')
        experiment = re.match(r'^NDEAEvolve\.(Exp\d{3})(?:\.|$)', row['name'])
        require(experiment is not None, f'Nonproject declaration: {row}')
        entry = dict(row, experiment=experiment[1], source_path=path,
                     source_sha256=marker['source_sha256'], source_line=original_row['line'],
                     combined_source=str(SOURCE), combined_line=row['line'],
                     source_marker_line=marker['marker_line'])
        del entry['line']
        (private if row['private'] else public).append(entry)
    existing = re.findall(r'^\s*#print axioms (\S+)\s*$', lexer.code_only(original), re.M)
    names = [row['name'] for row in public]
    expected008 = json.loads((ROOT / 'evidence/FINAL_INPUTS.json').read_text())['expected_audits']
    require(len(existing) == len(set(existing)) == 90, 'Existing audit count is not exactly 90')
    require(existing == expected008, 'Existing audits differ from sealed catalog')
    require(set(existing) == {row['name'] for row in public if row['experiment'] == 'Exp008'},
            'Exp008 public source inventory differs from sealed audit list')
    counts = {f'Exp{i:03d}': sum(row['experiment'] == f'Exp{i:03d}' for row in public)
              for i in range(1, 9)}
    modules = []
    for path in source_cache:
        relevant = [row for row in public + private if row['source_path'] == path]
        modules.append({'source_path': path, 'source_sha256': sha(Path(path)),
                        'experiment': relevant[0]['experiment'],
                        'public_declarations': sum(not row['private'] for row in relevant),
                        'private_declarations': sum(row['private'] for row in relevant),
                        'combined_first_declaration_line': min(row['combined_line'] for row in relevant),
                        'combined_last_declaration_line': max(row['combined_line'] for row in relevant)})
    supplement = [name for name in names if name not in set(existing)]
    record = {'scope': 'Every public project theorem/lemma declared in the sealed Exp008 combined source; excludes private declarations, definitions, external-library declarations, and absent historical modules.',
              'combined_source': str(SOURCE), 'combined_sha256': EXPECTED_SHA,
              'public_declarations': len(public), 'private_declarations_excluded': len(private),
              'per_experiment_public_counts': counts, 'existing_audit_count': len(existing),
              'additional_audit_count': len(supplement),
              'expected_complete_audit_names': names,
              'existing_audit_names': existing, 'additional_audit_names': supplement,
              'inventory_status': 'Source inventory verified; new Lean run required to accept proposed complete audit list.',
              'validation': {'comments_and_strings_removed': True,
                             'all_theorem_lemma_tokens_accounted_for': True,
                             'named_namespaces_and_sections_balanced': True,
                             'anonymous_noncomputable_sections_open_at_eof': len(anonymous_sections),
                             'all_marked_original_sources_match_recorded_sha256': True,
                             'each_declaration_resolves_in_original_source': True,
                             'exp008_public_inventory_matches_sealed_90_audits': True},
              'modules': modules, 'source_markers': markers,
              'declarations': public, 'excluded_private_declarations': private,
              'inventory_script_sha256': sha(Path(__file__))}
    (OUT / 'ALL_PUBLIC_THEOREMS.json').write_text(json.dumps(record, indent=2) + '\n')
    (OUT / 'ADDITIONAL_AXIOM_PRINTS.lean.txt').write_text(
        '\n'.join('#print axioms ' + name for name in supplement) + '\n')
    print(json.dumps({key: record[key] for key in ['public_declarations', 'private_declarations_excluded',
          'per_experiment_public_counts', 'existing_audit_count', 'additional_audit_count']}))


if __name__ == '__main__':
    main()
