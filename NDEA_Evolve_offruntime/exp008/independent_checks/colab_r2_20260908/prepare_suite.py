"""Package unchanged historical proof bodies and the retained audit overlay."""
from pathlib import Path
import hashlib,io,json,shutil,tarfile

root=Path(__file__).resolve().parent;exp=root.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventory=json.loads((root/'ALL_PUBLIC_THEOREMS.json').read_text())
base=exp/'lean/Exp008Combined.lean'
if sha(base)!=inventory['combined_sha256']:raise RuntimeError('Sealed source changed')
payload=root/'suite_payload';payload.mkdir(exist_ok=False)
shutil.copytree(root/'historical_inputs',payload/'historical_inputs')
for name in ['ALL_PUBLIC_THEOREMS.json','ADDITIONAL_AXIOM_PRINTS.lean.txt','build_audit_inventory.py']:
    shutil.copyfile(root/name,payload/name)
(payload/'sealed').mkdir();shutil.copyfile(base,payload/'sealed/Exp008Combined.lean')
overlay=payload/'AllCheckpointAudit.lean'
overlay.write_bytes(base.read_bytes()+b'\n-- Additional public predecessor audits for the fresh VM recheck.\n'+
                    (root/'ADDITIONAL_AXIOM_PRINTS.lean.txt').read_bytes())
case={'name':'AllCheckpointAudit','file':overlay.name,'source_sha256':sha(overlay),
      'expectation':'pass','expected_audits':inventory['expected_complete_audit_names']}
history=json.loads((payload/'historical_inputs/HISTORICAL_INPUTS.json').read_text())
checks=[case]
for old in history['checks']:
    row=dict(old);row['file']='historical_inputs/'+old['file']
    if 'error_line_ranges' in row:
        row['error_line_ranges']=[[item['first_line'],item['last_line']] for item in row['error_line_ranges']]
    checks.append(row)
names=[n for c in checks if c['expectation']=='pass' for n in c['expected_audits']]
if len(names)!=473 or len(set(names))!=473:raise RuntimeError('Unexpected complete audit coverage')
files={str(p.relative_to(payload)):sha(p) for p in sorted(payload.rglob('*')) if p.is_file()}
inputs={'checks':checks,'source_files':files,'public_audits':len(names),
        'expected_false_claim_rejections':sum(c.get('expected_error_count',0) for c in checks),
        'sealed_combined_sha256':inventory['combined_sha256'],
        'scope':'Retained source with extra audits plus exact accepted historical proof bodies and intended rejection controls.'}
text=json.dumps(inputs,indent=2)+'\n'
(root/'SUITE_INPUTS.json').write_text(text);(payload/'SUITE_INPUTS.json').write_text(text)
files['SUITE_INPUTS.json']=sha(payload/'SUITE_INPUTS.json')
archive=root/'historical_suite_sources.tar.gz'
with tarfile.open(archive,'x:gz') as tar:
    for name in sorted(files):
        data=(payload/name).read_bytes();item=tarfile.TarInfo(name);item.size=len(data);item.mode=0o644
        tar.addfile(item,io.BytesIO(data))
request={'archive':'/content/exp008_check/'+archive.name,'sha256':sha(archive),'files':files,
         'runner_sha256':sha(root/'verify_suite.py')}
(root/'SUITE_UPLOAD.json').write_text(json.dumps(request,indent=2)+'\n')
print(json.dumps({'archive':str(archive),'sha256':request['sha256'],'checks':len(checks),
                  'public_audits':len(names),'rejections':inputs['expected_false_claim_rejections']}))
