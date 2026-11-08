#!/usr/bin/env python3
"""Combined-source check of a fixed, already modular-verified closure. Not an Exp016 seal."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

BASELINE = '5e2b5522bf7ddee673b040c64ba28e3863d94b38'
BASE = 'NDEA_Evolve_offruntime/exp016'
MODULE = 'Exp016ConvergenceCombined'
IMPORT = re.compile(r'^import\s+([A-Za-z_][\w.\']*)\s*$')
SCOPE = re.compile(r'^(namespace|(?:noncomputable\s+)?section)(?:\s+(\S+))?\s*$')
END = re.compile(r'^end(?:\s+(\S+))?\s*$')
DECL = re.compile(r'^(?:@\[[^\]]+\]\s*)?(?:(private|protected)\s+)?(?:theorem|lemma)\s+([^\s(:]+)')
EXTERNAL = {'Mathlib','Init','Lean','Std','Batteries','Aesop','Qq','ProofWidgets','Plausible','LeanSearchClient','ImportGraph'}


def require(ok: bool, message: str) -> None:
    if not ok: raise ValueError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(['git','-C',str(repo),*args], text=True).strip()


def save(out: Path, name: str, value: dict) -> None:
    (out/name).write_text(json.dumps(value,indent=2)+'\n')


def code_only(text: str) -> str:
    """Mask nested comments and strings without moving character or line positions."""
    out=list(text); i=depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i): out[i:i+2]='  ';depth+=1;i+=2
            elif text.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
            else:
                if text[i]!='\n':out[i]=' '
                i+=1
        elif text.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif text.startswith('--',i):
            while i<len(text) and text[i]!='\n':out[i]=' ';i+=1
        elif text[i]=='"':
            out[i]=' ';i+=1;closed=False
            while i<len(text):
                c=text[i]
                if c!='\n':out[i]=' '
                i+=1
                if c=='\\' and i<len(text):
                    if text[i]!='\n':out[i]=' '
                    i+=1
                elif c=='"':closed=True;break
            require(closed,'Unterminated string')
        else:i+=1
    require(depth==0,'Unterminated comment')
    return ''.join(out)


def transform(text: str, module: str, seen: set[str]) -> tuple[str,list[str],list[str],dict]:
    """Keep every proof-body byte; remove only reviewed one-line diagnostic/import commands."""
    clean=code_only(text)
    require(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|elab|initialize|macro|run_tac)\b',clean),
            'Unsupported proof escape or executable extension: '+module)
    stack=[];external=[];names=[];body=[];removed=[]
    originals=text.splitlines(keepends=True);masked=clean.splitlines(keepends=True)
    require(len(originals)==len(masked),'Line masking mismatch')
    for number,(original,line) in enumerate(zip(originals,masked),1):
        command=line.strip()
        if match:=IMPORT.fullmatch(command):
            name=match[1]
            if name.split('.')[0] in EXTERNAL:external.append(name)
            else:require(name in seen,'Unresolved or out-of-order project import: '+name)
            removed.append({'line':number,'kind':'import','module':name});body.append('\n');continue
        if line == line.lstrip() and re.match(r'^(?:public\s+|private\s+|meta\s+)?import\b|^module\b',command):
            raise ValueError('Unsupported import/module syntax: '+module)
        if re.fullmatch(r'#print\s+axioms\s+\S+|#check\s+\S+',command):
            removed.append({'line':number,'kind':'diagnostic'});body.append('\n');continue
        if command.startswith('#'):
            raise ValueError('Unsupported diagnostic command: '+module+': '+command)
        if match:=SCOPE.fullmatch(command):
            kind='namespace' if match[1]=='namespace' else 'section'
            require(kind!='namespace' or match[2] is not None,'Anonymous namespace')
            stack.append((kind,match[2]))
        elif match:=END.fullmatch(command):
            require(bool(stack),'Unmatched end: '+module)
            kind,name=stack.pop()
            require(match[1] is None or match[1]==name,'Mismatched named end: '+module)
        if match:=DECL.match(command):
            if match[1]!='private':
                name=match[2]
                require(not name.startswith('_root_.'),'Root-qualified theorem needs review')
                names.append('.'.join([n for kind,n in stack if kind=='namespace']+[name]))
        elif re.match(r'^(?:@\[[^\]]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\b',command):
            raise ValueError('Unsupported theorem declaration: '+module+': '+command)
        body.append(original)
    require(all(kind=='section' and name is None for kind,name in stack),'Unclosed named scope: '+module)
    # Every remaining anonymous section was implicitly closed at the original EOF.
    retained=''.join(body)
    section='CombinedSource_'+module.replace('.','_')
    result=(f'\n-- SOURCE {module} SHA256 {digest(text)}\nsection {section}\n'+retained+
            '\n'+'end\n'*len(stack)+f'end {section}\n')
    return result,external,names,{'module':module,'source_sha256':digest(text),'body_sha256':digest(retained),
                                 'removed_directives':removed,'implicit_eof_sections':len(stack)}


def generate(rows: list[tuple[str,str]]) -> tuple[str,dict]:
    seen=set();external=set();names=[];bodies=[];records=[]
    for module,text in rows:
        require(module not in seen,'Duplicate module')
        body,imports,public,record=transform(text,module,seen)
        bodies.append(body);external.update(imports);names+=public;records.append(record);seen.add(module)
    require(len(names)==len(set(names)),'Duplicate public declaration')
    require(bool(names),'Empty theorem catalog')
    source=('\n'.join('import '+name for name in sorted(external))+'\n'+''.join(bodies)+
            '\n'+'\n'.join('#print axioms '+name for name in names)+'\n')
    return source,{'module':MODULE,'external_imports':sorted(external),'public_theorems':names,
                   'sources':records,'combined_sha256':digest(source)}


def load_tools(repo: Path):
    # Never silently modify the verification tools which produced the known successful checkpoint.
    paths=[BASE+'/verification_initial_error/check_initial_error_transfer.py']
    paths += [BASE+'/verification_convergence/'+name for name in
              ['run_assurance.py','evidence_audit.py','replay_environment.py']]
    for path in paths:
        committed=subprocess.check_output(['git','-C',str(repo),'show',BASELINE+':'+path])
        require(committed==(repo/path).read_bytes(),'Verified tool changed: '+path)
    sys.path.insert(0,str(repo/BASE/'verification_convergence'))
    spec=importlib.util.spec_from_file_location('retained_assurance',repo/BASE/'verification_convergence/run_assurance.py')
    driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)
    return driver,driver.load_builder(repo)


def baseline_sources(repo: Path, builder) -> list[dict]:
    sources=builder.resolve(repo)
    require(len(sources)==96,'Verified convergence closure changed size')
    for path in [x['path'] for x in sources]+list(builder.PINS)+[BASE+'/verification_convergence/VerificationContracts.lean']:
        committed=subprocess.check_output(['git','-C',str(repo),'show',BASELINE+':'+path])
        require(committed==(repo/path).read_bytes(),'Verified mathematical source or pin changed: '+path)
    return sources


def prepare(repo: Path,out: Path) -> None:
    driver,builder=load_tools(repo);baseline_sources(repo,builder)
    driver.validate_inputs(repo,builder);builder.prepare(repo,out)
    plan=json.loads((out/'plan.json').read_text())
    rows=[(x['module'],(repo/x['path']).read_text()) for x in plan['sources']]
    rows.append(('VerificationContracts',(repo/BASE/'verification_convergence/VerificationContracts.lean').read_text()))
    source,record=generate(rows)
    require(set(driver.evidence.EXPECTED)<=set(record['public_theorems']),'Missing target contract/theorem catalog')
    (out/'sources'/'VerificationContracts.lean').write_text(rows[-1][1])
    (out/'sources'/f'{MODULE}.lean').write_text(source)
    record.update(baseline_commit=BASELINE,commit=plan['commit'],generator_sha256=sha(Path(__file__)),
                  contract_sha256=sha(repo/BASE/'verification_convergence/VerificationContracts.lean'),
                  status='PREPARED_NOT_COMPILED',scope='97 source units: verified 96-module closure plus unchanged contracts; not all Exp016 controls')
    save(out,'COMBINED_INPUTS.json',record)
    print(json.dumps({'prepared_source_units':len(rows),'catalog_theorems':len(record['public_theorems']),
                      'combined_sha256':record['combined_sha256'],'status':record['status']}))


def run(repo: Path,out: Path) -> None:
    driver,builder=load_tools(repo);baseline_sources(repo,builder)
    plan=json.loads((out/'plan.json').read_text());builder.unchanged(repo,plan)
    inputs=json.loads((out/'COMBINED_INPUTS.json').read_text())
    rows=[(x['module'],(repo/x['path']).read_text()) for x in plan['sources']]
    rows.append(('VerificationContracts',(repo/BASE/'verification_convergence/VerificationContracts.lean').read_text()))
    regenerated,catalog=generate(rows);source=out/'sources'/f'{MODULE}.lean'
    require(source.read_text()==regenerated and sha(source)==inputs['combined_sha256'],'Combined source reconstruction mismatch')
    require(catalog['public_theorems']==inputs['public_theorems'],'Catalog reconstruction mismatch')
    require(sha(Path(__file__))==inputs['generator_sha256'],'Generator changed')
    deps=out/'deps'
    for path,value in plan['pins'].items():require(sha(deps/path)==value,'Bootstrap changed pin: '+path)
    lean=Path(subprocess.check_output(['elan','which','lean'],cwd=deps,text=True).strip()).resolve()
    require(sha(lean)==builder.LEAN_SHA256,'Compiler hash mismatch')
    checker=lean.with_name('leanchecker');require(checker.is_file(),'Missing pinned replay executable')
    packages=json.loads((deps/'lake-manifest.json').read_text())['packages']
    def package_check():
        for package in packages:
            path=deps/'.lake/packages'/package['name']
            require(git(path,'rev-parse','HEAD')==package['rev'],'Package revision mismatch')
            require(not git(path,'status','--porcelain','--untracked-files=no'),'Tracked package mutation')
    package_check()
    external=[deps/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in packages]+[lean.parent.parent/'lib/lean']
    from replay_environment import pinned_replay_environment
    env=pinned_replay_environment(lean,os.environ,builder.LEAN_SHA256,(deps/'lean-toolchain').read_text().strip())
    env.update(LEAN_PATH=os.pathsep.join(map(str,external)),LEAN_NUM_THREADS='1')
    objects=out/'combined-olean';objects.mkdir(exist_ok=False)
    receipt=driver.command(out,'combined-compile',[str(lean),'-j','1','-R',str(out/'sources'),'-o',str(objects/f'{MODULE}.olean'),str(source)],out/'sources',env,1800)
    require(receipt['exit_code']==0,'Combined elaboration failed; inspect combined-compile.log')
    reports=driver.evidence.parse_axioms((out/'combined-compile.log').read_text(),inputs['public_theorems'])
    require(set(driver.evidence.EXPECTED)<=set(reports),'Missing required target audit')
    env['LEAN_PATH']=os.pathsep.join(map(str,[objects,*external]))
    replay=driver.command(out,'combined-replay',[str(checker),'--fresh','--verbose',MODULE],out/'sources',env,1200)
    require(replay['exit_code']==0,'Combined fresh replay failed or timed out')
    require(f'replaying {MODULE} with --fresh' in (out/'combined-replay.log').read_text(),'Missing replay marker')
    builder.unchanged(repo,plan);baseline_sources(repo,builder);package_check()
    require(source.read_text()==regenerated,'Combined source changed during verification')
    require(sha(lean)==builder.LEAN_SHA256,'Compiler changed')
    save(out,'COMBINED_RESULT.json',{'status':'COMBINED_SOURCE_AND_FRESH_REPLAY_PASS','commit':plan['commit'],
        'baseline_commit':BASELINE,'source_units':97,'public_theorems_audited':len(reports),'target_declarations':len(driver.evidence.EXPECTED),
        'source_sha256':sha(source),'olean_sha256':sha(objects/f'{MODULE}.olean'),
        'compile_log_sha256':sha(out/'combined-compile.log'),'replay_log_sha256':sha(out/'combined-replay.log'),
        'lean_sha256':sha(lean),'leanchecker_sha256':sha(checker),'compilation_external_paths':list(map(str,external)),
        'project_olean_imports_during_compilation':False,'independent_kernel':False,'exp016_sealed':False,
        'finished_utc':datetime.now(timezone.utc).isoformat()})
    save(out,'COMBINED_EVIDENCE_MANIFEST.json',{'files':{str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*'))
          if p.is_file() and p.relative_to(out).parts[0]!='deps' and p.name!='COMBINED_EVIDENCE_MANIFEST.json'}})
    print('COMBINED_SOURCE_AND_FRESH_REPLAY_PASS; no independent-kernel or Exp016 seal claim.')


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['prepare','run'])
    parser.add_argument('--repo',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);a=parser.parse_args()
    repo,out=a.repo.resolve(),a.output.resolve()
    require(repo!=out and repo not in out.parents,'Output must be outside checkout')
    if a.mode=='prepare':require(not out.exists(),'Refusing output overwrite')
    else:require(not (out/'COMBINED_RESULT.json').exists(),'Refusing completed-result overwrite')
    try:(prepare if a.mode=='prepare' else run)(repo,out)
    except Exception as exc:
        if out.is_dir():save(out,'COMBINED_FAILURE.json',{'status':'BLOCKED_OR_FAILED','error':str(exc)})
        print('BLOCKED_OR_FAILED:',exc,file=sys.stderr);return 1
    return 0


if __name__=='__main__':raise SystemExit(main())
