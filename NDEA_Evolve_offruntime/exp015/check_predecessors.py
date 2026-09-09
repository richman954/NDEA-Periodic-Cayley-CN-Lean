"""Verify the frozen predecessor manifests without modifying predecessor files."""
import argparse,datetime,hashlib,json
from pathlib import Path

root=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=Path,default=root/'evidence/PREDECESSOR_PRESERVATION.json')
args=p.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
previous_root=root.parent/'exp014'
previous_manifest=previous_root/'PACKET_MANIFEST.json'
if sha(previous_manifest)!='8779d9e4732613d19b2b5efa5ea5eee098664383d3e924e7fe304830627b98a6':
    raise RuntimeError('Frozen Experiment 014 manifest changed')
previous_entries=json.loads(previous_manifest.read_text())
previous_receipt=previous_root/'evidence/PREDECESSOR_PRESERVATION.json'
if sha(previous_receipt)!=previous_entries['evidence/PREDECESSOR_PRESERVATION.json']:
    raise RuntimeError('Frozen predecessor receipt changed')
previous=json.loads(previous_receipt.read_text())
checks=[]
for old in previous['checks']:
    base=Path(old['root']);manifest=Path(old['manifest_path'])
    fmt=old.get('manifest_format', 'json' if manifest.suffix=='.json' else 'sha256sum')
    if fmt not in ['json','sha256sum']:raise RuntimeError('Unknown predecessor manifest format')
    checks.append((old['name'],base,manifest,fmt,old['expected_entry_count'],old['manifest_sha256_after']))
checks.append(('exp014_final_packet',previous_root,previous_manifest,'json',262,
    '8779d9e4732613d19b2b5efa5ea5eee098664383d3e924e7fe304830627b98a6'))
record={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope':'Read-only hash checks of frozen source/evidence manifests; no predecessor proof compilation or edit.',
        'checks':[],'passed':False}
for name,base,manifest,fmt,count,expected in checks:
    before=sha(manifest)
    if fmt=='json':
        d=json.loads(manifest.read_text());entries=d.get('files',d)
    else:
        entries={}
        for line in manifest.read_text().splitlines():
            if not line.strip():continue
            digest,filename=line.split(maxsplit=1)
            filename=filename.removeprefix('*')
            if filename in entries:raise RuntimeError('Duplicate manifest entry')
            entries[filename]=digest
    failures=[]
    for filename,digest in entries.items():
        path=base/filename
        if not path.is_file() or sha(path)!=digest:failures.append(filename)
    after=sha(manifest)
    result={'name':name,'root':str(base),'manifest_path':str(manifest),'manifest_format':fmt,'expected_manifest_sha256':expected,
            'manifest_sha256_before':before,'manifest_sha256_after':after,'expected_entry_count':count,
            'entry_count':len(entries),'matched_entry_count':len(entries)-len(failures),'failures':failures,
            'passed':before==after==expected and len(entries)==count and not failures}
    record['checks'].append(result)
archive_pins={
    '/home/richman954/Exp008_Verified_Review_Packet_20260908.zip':
        '8e2b429c161443901be17a585562af2ce5f920b44283044ba3e5f14bd99330a7',
    '/home/richman954/Experiments_001-008_Fresh_VM_Recheck_20260908.zip':
        '95f8fc6d27975d0a59fbea3f9e0a6517369131342d8abbdecb9923606d545a4c',
    '/home/richman954/Exp009_Verified_Review_Packet_20260908.zip':
        '1ecbfe8203e1082ee8e89647e01a0c90aad3f366dcdc4dc797fea43d7b6d520c',
    '/home/richman954/Exp010_Verified_Review_Packet_20260908.zip':
        '91f4069711cc3ab26978d89eb9f12a2853524609e48d53c01e73eddbf74fd438',
    '/home/richman954/Exp011_Verified_Review_Packet_20260908.zip':
        'f6f52467bbed628201cc02f740a6203cb1b0ad57b3b257a8a89a1779e223cac3',
    '/home/richman954/Exp012_Verified_Review_Packet_20260908.zip':
        '2c1347c1261c00f1f63e06b7c500235c48dfb5e9b817f25ffb23ea0edc0d596d',
    '/home/richman954/Exp013_Verified_Review_Packet_20260908.zip':
        'dbaad9c12c0f5154099f6ccaac3e1675fb6b678eb1ccb37d7f601e252dcf6412',
    '/home/richman954/Exp014_Verified_Review_Packet_20260909.zip':
        '11aed98c23b9a5efc64e9f66d042d61ff08c1f33e76c4b8889174f299b56b282'}
record['archive_checks']=[{'path':name,'expected_sha256':digest,'sha256':sha(Path(name)),
    'passed':sha(Path(name))==digest} for name,digest in archive_pins.items()]
record['passed']=all(x['passed'] for x in record['checks']+record['archive_checks'])
record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
args.output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'passed':record['passed'],'checks':[{k:x[k] for k in ['name','entry_count','matched_entry_count','passed']} for x in record['checks']]},indent=2))
if not record['passed']:raise SystemExit(1)
