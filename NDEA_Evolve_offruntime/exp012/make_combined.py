"""Inline all frozen/project proof source; emit a complete public axiom audit."""
import hashlib,importlib.util,json,re
from pathlib import Path

def require(ok,message):
    if not ok:raise RuntimeError(message)

def build(root):
    foundation=root/'lean/Exp011Foundation.lean'
    require(hashlib.sha256(foundation.read_bytes()).hexdigest()=='6e516d1a5cbd1eae23feddcb9b26a29c12a15a6a0d45928c891acd9be453e3e5','Frozen foundation pin mismatch')
    modules=['EnergyLocal','EnergyConservation','EnergySeparation','ClassicalUniqueness','Controls']
    embedded=['Exp011Foundation','InfiniteReference','WeightedTail','CutoffSchedule',
              'InfiniteClosure','WeightedClosure','ScheduleClosure','SuperpositionClosure',
              'Regularity','ClassicalSolution','Continuity','ClassicalClosure',
              'SolutionLipschitz','Reconstruction','ScheduleBounds','UniformConvergence']
    checker=root/'verification_tools/verify_exp005.py'
    require(hashlib.sha256(checker.read_bytes()).hexdigest()=='fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb','Catalog scanner pin mismatch')
    spec=importlib.util.spec_from_file_location('exp012_catalog_policy',checker)
    policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
    files=[foundation]+[root/'lean'/(m+'.lean') for m in modules]
    require(all(p.is_file() for p in files),'Missing production/control source')
    imports=set();bodies=[];names=[];hashes={}
    for p in files:
        s=p.read_text();hashes[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
        clean=policy.code_only(s)
        for m in re.findall(r'^import (\S+)',clean,re.M):
            if m.startswith(('Mathlib.','Lean.','Std.','Init.')):imports.add(m)
            else:require(m in modules+embedded,'Unexpected project import: '+m)
        if p!=foundation:
            stack=[]
            for line in clean.splitlines():
                line=line.strip()
                if m:=re.match(r'^namespace (\S+)',line):stack.append(('namespace',m[1]))
                elif m:=re.match(r'^section(?: (\S+))?\s*$',line):stack.append(('section',m[1]))
                elif re.match(r'^end(?: \S+)?\s*$',line):
                    require(bool(stack),'Unmatched end in '+str(p)+': '+line)
                    stack.pop()
                if m:=re.match(r'^(?:@\[[^\]]+\]\s*)?(?:(private|protected)\s+)?(?:theorem|lemma)\s+([^\s(:]+)',line):
                    if m[1]!='private':
                        names.append('.'.join([name for kind,name in stack if kind=='namespace']+[m[2]]))
                elif re.match(r'^(?:@\[[^\]]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\b',line):
                    raise RuntimeError('Unsupported declaration format in '+str(p)+': '+line)
            require(not stack,'Unclosed namespace/section in '+str(p))
        s=re.sub(r'^(?:import |#print axioms |#check ).*\n','',s,flags=re.M)
        bodies.append('-- SOURCE '+str(p.relative_to(root))+' SHA256 '+hashes[str(p.relative_to(root))]+'\n'+s)
    require(len(names)==len(set(names)),'Duplicate public theorem/lemma audit name')
    combined='\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
    receipt={'source_sha256':hashlib.sha256(combined.encode()).hexdigest(),'source_hashes':hashes,'expected_audits':names,'external_imports':sorted(imports),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    return combined,receipt

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    combined,receipt=build(root)
    out=root/'lean/Exp012Combined.lean';out.write_text(combined)
    (root/'evidence/FINAL_INPUTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'combined':str(out),'sha256':receipt['source_sha256'],'audits':len(receipt['expected_audits'])}))
