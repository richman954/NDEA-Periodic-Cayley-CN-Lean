"""Reconstruct the exact Exp014 foundation and audit only new Exp015 declarations."""
import hashlib
import importlib.util
import json
import re
from pathlib import Path

PREDECESSORS = {
    'Exp014Combined': '40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee',
}
FOUNDATION_SHA256 = '9d8ac0dfcba35dec86ea229657defc88da01f94ddfece9b8f119f52120a4d8c6'
MODULES = ['ScalarSqrtEstimate', 'SpatialL2', 'ResidualField', 'ForcedStability', 'ResidualEstimate',
           'VariablePotentialBridge', 'Controls']
EMBEDDED_PREDECESSOR_MODULES = {
    'GenericClassical', 'GenericEnergy', 'GenericUniqueness',
    'StrongOperatorDerivative', 'GlobalLinearEvolution', 'WeightedFourier',
    'ScalarSeries', 'FourierPotential', 'FourierSynthesis', 'FourierProduct',
    'ClassicalExistence', 'Exp013GenericFoundation', 'Exp014Foundation', 'Exp014Combined',
}
EXTERNAL_PREFIXES = ('Mathlib.', 'Lean.', 'Std.', 'Init.')


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def policy_for(root):
    checker = root/'verification_tools/verify_exp005.py'
    require(sha(checker) == 'fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb',
            'Catalog scanner pin mismatch')
    spec = importlib.util.spec_from_file_location('exp015_catalog_policy', checker)
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    return policy


def strip_directives(source):
    return re.sub(r'^(?:import |#print axioms |#check ).*\n', '', source, flags=re.M)


def build_foundation(root):
    """Strip only the 143 old axiom-print commands from the exact sealed combined source."""
    relative = 'predecessor_sources/Exp014Combined.lean'
    original = root/relative
    require(sha(original) == PREDECESSORS['Exp014Combined'], 'Exp014 combined predecessor pin mismatch')
    source = original.read_text()
    policy = policy_for(root)
    old_audits = re.findall(r'^#print axioms (\S+)', policy.code_only(source), re.M)
    require(len(old_audits) == len(set(old_audits)) == 143
            and all(name.startswith('NDEAEvolve.Exp014.') for name in old_audits),
            'Pinned predecessor audit catalog differs')
    foundation = re.sub(r'^#print axioms .*\n', '', source, flags=re.M)
    require(hashlib.sha256(foundation.encode()).hexdigest() == FOUNDATION_SHA256,
            'Derived Exp014 foundation pin mismatch')
    require(all(name.startswith(EXTERNAL_PREFIXES) for name in
                re.findall(r'^import (\S+)', policy.code_only(foundation), re.M)),
            'Predecessor foundation contains a project import')
    return foundation, {relative: PREDECESSORS['Exp014Combined']}


def public_names(clean, path):
    stack, names = [], []
    for line in clean.splitlines():
        line = line.strip()
        if match := re.match(r'^namespace (\S+)', line):
            stack.append(('namespace', match[1]))
        elif match := re.match(r'^section(?: (\S+))?\s*$', line):
            stack.append(('section', match[1]))
        elif re.match(r'^end(?: \S+)?\s*$', line):
            require(bool(stack), 'Unmatched end in '+str(path)+': '+line)
            stack.pop()
        if match := re.match(r'^(?:@\[[^\]]+\]\s*)?(?:(private|protected)\s+)?'
                             r'(?:theorem|lemma)\s+([^\s(:]+)', line):
            if match[1] != 'private':
                names.append('.'.join([n for kind, n in stack if kind == 'namespace']+[match[2]]))
        elif re.match(r'^(?:@\[[^\]]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                      r'(?:theorem|lemma)\b', line):
            raise RuntimeError('Unsupported declaration format in '+str(path)+': '+line)
    require(not stack, 'Unclosed namespace/section in '+str(path))
    require(all(name.startswith('NDEAEvolve.Exp015.') for name in names),
            'New declaration is outside the Exp015 namespace: '+str(path))
    return names


def build(root):
    foundation = root/'lean/Exp014Foundation.lean'
    reconstructed, predecessor_hashes = build_foundation(root)
    require(foundation.read_text() == reconstructed, 'Exp014 foundation reconstruction differs')
    policy = policy_for(root)
    files = [foundation]+[root/'lean'/(module+'.lean') for module in MODULES]
    require(all(path.is_file() for path in files), 'Missing production/control source')
    imports, bodies, names, hashes = set(), [], [], dict(predecessor_hashes)
    embedded = set(MODULES) | EMBEDDED_PREDECESSOR_MODULES
    for path in files:
        source = path.read_text()
        relative = str(path.relative_to(root))
        hashes[relative] = sha(path)
        clean = policy.code_only(source)
        for name in re.findall(r'^import (\S+)', clean, re.M):
            if name.startswith(EXTERNAL_PREFIXES):
                imports.add(name)
            else:
                require(name in embedded, 'Unexpected project import: '+name)
        if path != foundation:
            names.extend(public_names(clean, path))
        bodies.append('-- SOURCE '+relative+' SHA256 '+hashes[relative]+'\n'+strip_directives(source))
    require(bool(names) and len(names) == len(set(names)), 'Empty or duplicate public theorem/lemma catalog')
    combined = ('\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)
                +'\n\n'+'\n'.join('#print axioms '+name for name in names)+'\n')
    receipt = {'source_sha256': hashlib.sha256(combined.encode()).hexdigest(),
               'source_hashes': hashes, 'expected_audits': names,
               'external_imports': sorted(imports), 'generator_sha256': sha(Path(__file__)),
               'retained_predecessor_source_hashes': predecessor_hashes,
               'foundation_scope': 'Exact sealed Exp014 combined proof bodies, retaining its generic '
                   'Exp013 foundation and all Exp014 mathematics; only its 143 axiom-print commands '
                   'are removed. The audit catalog covers only new Exp015 declarations. Earlier '
                   'numerical proof chains remain outside this combined source.'}
    return combined, receipt


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    combined, receipt = build(root)
    output = root/'lean/Exp015Combined.lean'
    output.write_text(combined)
    (root/'evidence/FINAL_INPUTS.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'combined': str(output), 'sha256': receipt['source_sha256'],
                      'audits': len(receipt['expected_audits'])}))
