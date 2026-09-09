#!/usr/bin/env python3
"""Fresh combined kernel check and exact axiom audit for the Exp006 milestone."""
import datetime, hashlib, json, pathlib, re, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
names=['Exp005Foundation','PeriodicGrid','PeriodicModeResidual','Exp005ModeBridge','Controls']
paths=[root/'lean'/f'{n}.lean' for n in names]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
original={str(p):sha(p) for p in paths}
predecessor=pathlib.Path('/home/richman954/NDEA_Evolve_offruntime/exp005/worktree/NDEA_Evolve')
combiner=predecessor/'experiments/exp005_mesh_weighted_residual_bridge/assurance/make_combined_verification.py'
reproduction=root/'evidence/Exp005FoundationReproduced.lean'
subprocess.run([sys.executable,str(combiner),'--repo',str(predecessor),'--output',str(reproduction)],check=True)
if sha(reproduction)!=sha(paths[0]): raise RuntimeError('Frozen Exp005 foundation reproduction mismatch')
mathlib=pathlib.Path('/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages/mathlib')
commit=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
if commit!='fabf563a7c95a166b8d7b6efca11c8b4dc9d911f': raise RuntimeError('Mathlib revision mismatch')
if subprocess.check_output(['git','-C',str(mathlib),'status','--porcelain=v1','--untracked-files=no'],text=True):
    raise RuntimeError('Mathlib tracked source dirty')
imports=set()
chunks=[]
for p in paths:
    text=p.read_text()
    for line in text.splitlines():
        if line.startswith('import '):
            module=line.split()[1]
            if module.startswith(('Mathlib.','Lean.')): imports.add(module)
    # No placeholder/custom axiom/foreign evaluation is permitted in a source declaration.
    forbidden=r'^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide|unsafeCast|implemented_by)\b'
    clean=re.sub(r'/\-.*?\-/','',text,flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    if re.search(forbidden,clean,re.M): raise RuntimeError(f'Forbidden proof construction in {p}')
    lines=[line for line in text.splitlines() if not line.startswith('import ') and not line.lstrip().startswith(('#print','#check'))]
    chunks.append(f'\n-- SOURCE {p.name} SHA256 {sha(p)}\n'+'\n'.join(lines)+'\n')
expected=[]
for name,p in zip(names,paths):
    if name=='Exp005Foundation': continue
    namespace='NDEAEvolve.Exp006'
    if name=='PeriodicGrid': namespace+='.PeriodicGrid'
    if name=='Controls': namespace+='.Controls'
    declarations=re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9]*)',p.read_text(),re.M)
    expected.extend(namespace+'.'+d for d in declarations)
if len(set(expected))!=len(expected): raise RuntimeError('Duplicate expected theorem')
(root/'evidence/EXPECTED_FINAL_THEOREMS.json').write_text(json.dumps(expected,indent=2)+'\n')
combined=root/'lean/CombinedVerification.lean'
combined.write_text(''.join('import '+m+'\n' for m in sorted(imports))+''.join(chunks)+'\n'+''.join('#print axioms '+n+'\n' for n in expected))
# Each symlink exposes only an external namespace; project artifact names are absent.
isolated=root/'isolated_dependencies'
isolated.mkdir(exist_ok=True)
for name in ['Mathlib','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible']:
    for suffix in ['', '.olean', '.olean.private', '.olean.server', '.ir']:
        src=root/'build/lib/lean'/(name+suffix)
        dst=isolated/(name+suffix)
        if src.exists() and not dst.exists(): dst.symlink_to(src,target_is_directory=src.is_dir())
before=set((root/'evidence').glob('*CombinedVerification.json'))
result=subprocess.run([sys.executable,str(root/'run_lean.py'),'lean/CombinedVerification.lean'],cwd=root)
after=set((root/'evidence').glob('*CombinedVerification.json'))
receipts=after-before
if len(receipts)!=1: raise RuntimeError('Expected one final receipt')
receipt=receipts.pop()
rec=json.loads(receipt.read_text())
log=pathlib.Path(rec['log'])
text=log.read_text()
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
seen={}
for name,body in rows:
    if name in seen: raise RuntimeError('Duplicate axiom audit '+name)
    seen[name]=[a.strip() for a in body.split(',') if a.strip()]
allowed={'propext','Classical.choice','Quot.sound'}
passed=(result.returncode==0 and rec['sources_unchanged'] and
        set(seen)==set(expected) and all(set(a)<=allowed for a in seen.values()) and
        original=={str(p):sha(p) for p in paths})
report={'passed':passed,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope':'Concrete nonzero periodic first Fourier mode, commuting A=B=negative centered Laplacian; actual Exp005 residual and fixed-time bridge.',
        'expected_theorem_count':len(expected),'audited_theorem_count':len(seen),'axioms':seen,
        'source_sha256':original,'frozen_foundation_reproduction_sha256':sha(reproduction),'frozen_combiner_sha256':sha(combiner),'combined_sha256':sha(combined),'receipt':str(receipt),
        'receipt_sha256':sha(receipt),'log_sha256':sha(log),'verifier_sha256':sha(pathlib.Path(__file__)),
        'project_artifacts_excluded_from_final_import_path':True,
        'external_imports':sorted(imports),'lean_binary_sha256':rec['lean_binary_sha256'],
        'mathlib_commit':rec['mathlib_commit']}
(root/'evidence/FINAL_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':passed,'audited':len(seen),'expected':len(expected),'report':str(root/'evidence/FINAL_VERIFICATION.json')},indent=2))
if not passed: raise SystemExit(1)
