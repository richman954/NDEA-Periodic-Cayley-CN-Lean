"""Reconstruct the pinned generic foundation and audit every new public theorem."""
import hashlib, importlib.util, json, re
from pathlib import Path

PREDECESSORS = {
    'GenericClassical': '26198a2e7dbc815ef665c663c1c3c991cba5926a67ac1e5361530db1c4ee33ec',
    'GenericEnergy': 'f1668d4704a8527839e8ffec5fff535b923c12e28285be7434ac62045d64dece',
    'GenericUniqueness': '93d1fed2c93b69ff1d9614faaef4a7150e0a392cbe9e206e88b1cfefd451cab9',
}
MODULES = ['StrongOperatorDerivative', 'GlobalLinearEvolution', 'WeightedFourier',
           'ScalarSeries', 'FourierPotential', 'FourierSynthesis', 'FourierProduct',
           'ClassicalExistence', 'Controls']
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
    spec = importlib.util.spec_from_file_location('exp014_catalog_policy', checker)
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    return policy


def strip_directives(source):
    return re.sub(r'^(?:import |#print axioms |#check ).*\n', '', source, flags=re.M)


def build_foundation(root):
    """Retain exact generic predecessor bodies, checking all original file pins."""
    policy = policy_for(root)
    imports, bodies, hashes = set(), [], {}
    for module, digest in PREDECESSORS.items():
        relative = 'predecessor_sources/'+module+'.lean'
        path = root/relative
        require(sha(path) == digest, 'Generic predecessor pin mismatch: '+module)
        source = path.read_text()
        for name in re.findall(r'^import (\S+)', policy.code_only(source), re.M):
            if name.startswith(EXTERNAL_PREFIXES):
                imports.add(name)
            else:
                require(name in PREDECESSORS, 'Unexpected predecessor project import: '+name)
        hashes[relative] = digest
        bodies.append('-- SOURCE '+relative+' SHA256 '+digest+'\n'+strip_directives(source))
    source = '\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)+'\n'
    return source, hashes


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
    return names


def build(root):
    foundation = root/'lean/Exp013GenericFoundation.lean'
    reconstructed, predecessor_hashes = build_foundation(root)
    require(foundation.read_text() == reconstructed, 'Generic foundation reconstruction differs')
    policy = policy_for(root)
    files = [foundation]+[root/'lean'/(module+'.lean') for module in MODULES]
    require(all(path.is_file() for path in files), 'Missing production/control source')
    imports, bodies, names, hashes = set(), [], [], dict(predecessor_hashes)
    embedded = set(MODULES) | set(PREDECESSORS) | {'Exp013GenericFoundation'}
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
    require(len(names) == len(set(names)), 'Duplicate public theorem/lemma audit name')
    combined = ('\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)
                +'\n\n'+'\n'.join('#print axioms '+name for name in names)+'\n')
    receipt = {'source_sha256': hashlib.sha256(combined.encode()).hexdigest(),
               'source_hashes': hashes, 'expected_audits': names,
               'external_imports': sorted(imports), 'generator_sha256': sha(Path(__file__)),
               'retained_predecessor_source_hashes': predecessor_hashes,
               'foundation_scope': 'Only the pinned Exp013 generic classical, energy and uniqueness '
                                   'sources; no earlier numerical proof chain.'}
    return combined, receipt


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    combined, receipt = build(root)
    output = root/'lean/Exp014Combined.lean'
    output.write_text(combined)
    (root/'evidence/FINAL_INPUTS.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'combined': str(output), 'sha256': receipt['source_sha256'],
                      'audits': len(receipt['expected_audits'])}))
