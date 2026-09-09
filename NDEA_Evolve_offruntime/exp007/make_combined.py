"""Inline all frozen/project proof source; emit a complete public axiom audit."""
import hashlib,json,re
from pathlib import Path

def build(root):
    foundation=root/'foundation/Exp006CombinedVerification.lean'
    assert hashlib.sha256(foundation.read_bytes()).hexdigest()=='af3d14716b492f6485dd1bcf88c3c99cd13440a219f89b27b5258531d7f96c52'
    modules=['ReducedNoncommuting','SpinorGrid','ContinuumSpinor','ReducedClosure','FullClosure','StageBridge','Controls']
    files=[foundation]+[root/'lean'/(m+'.lean') for m in modules]
    assert all(p.is_file() for p in files)
    imports=set();bodies=[];names=[];hashes={}
    for p in files:
        s=p.read_text();hashes[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
        for m in re.findall(r'^import (\S+)',s,re.M):
            if m.startswith(('Mathlib.','Lean.','Std.','Init.')):imports.add(m)
            else:assert m in modules+['CombinedVerification']
        if p!=foundation:
            stack=[]
            for line in s.splitlines():
                if m:=re.match(r'^namespace (\S+)',line):stack.append(('namespace',m[1]))
                elif m:=re.match(r'^section(?: (\S+))?\s*$',line):stack.append(('section',m[1]))
                elif re.match(r'^end(?: \S+)?\s*$',line):
                    assert stack,(p,line)
                    stack.pop()
                if m:=re.match(r'^(?:@\[[^\]]+\]\s*)?(?:protected\s+)?theorem\s+(\w+)',line):
                    names.append('.'.join([name for kind,name in stack if kind=='namespace']+[m[1]]))
            assert not stack,(p,stack)
        s=re.sub(r'^(?:import |#print axioms |#check ).*\n','',s,flags=re.M)
        bodies.append('-- SOURCE '+str(p.relative_to(root))+' SHA256 '+hashes[str(p.relative_to(root))]+'\n'+s)
    assert len(names)==len(set(names))
    combined='\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
    receipt={'source_sha256':hashlib.sha256(combined.encode()).hexdigest(),'source_hashes':hashes,'expected_audits':names,'external_imports':sorted(imports),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    return combined,receipt

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    combined,receipt=build(root)
    out=root/'lean/Exp007Combined.lean';out.write_text(combined)
    (root/'evidence/FINAL_INPUTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'combined':str(out),'sha256':receipt['source_sha256'],'audits':len(receipt['expected_audits'])}))
