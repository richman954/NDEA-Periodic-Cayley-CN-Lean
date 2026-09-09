"""Verify the frozen predecessor manifests without modifying predecessor files."""
import argparse,datetime,hashlib,json
from pathlib import Path

root=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=Path,default=root/'evidence/PREDECESSOR_PRESERVATION.json')
args=p.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
previous=json.loads((root.parent/'exp008/evidence/PREDECESSOR_PRESERVATION.json').read_text())
checks=[]
for old in previous['checks']:
    base=Path(old['root']);manifest=Path(old['manifest_path'])
    fmt=old.get('manifest_format', 'json' if manifest.suffix=='.json' else 'sha256sum')
    if fmt not in ['json','sha256sum']:raise RuntimeError('Unknown predecessor manifest format')
    checks.append((old['name'],base,manifest,fmt,old['expected_entry_count'],old['manifest_sha256_after']))
checks += [
    ('exp008_final_packet',root.parent/'exp008',root.parent/'exp008/PACKET_MANIFEST.json','json',254,
     '537f3608ee3bdb96fadab042026ec722ec3c8957a1f0b1edf86be051b79ce4bd'),
    ('fresh_vm_recheck_r2',root.parent/'exp008/independent_checks/colab_r2_20260908',
     root.parent/'exp008/independent_checks/colab_r2_20260908/PACKET_MANIFEST.json','json',340,
     'abf5c23851a95eb69cfb70adf07e3b6038cd34655e140442e1e03fe32d0411a0')]
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
    result={'name':name,'root':str(base),'manifest_path':str(manifest),'expected_manifest_sha256':expected,
            'manifest_sha256_before':before,'manifest_sha256_after':after,'expected_entry_count':count,
            'entry_count':len(entries),'matched_entry_count':len(entries)-len(failures),'failures':failures,
            'passed':before==after==expected and len(entries)==count and not failures}
    record['checks'].append(result)
record['passed']=all(x['passed'] for x in record['checks'])
record['end_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
args.output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'passed':record['passed'],'checks':[{k:x[k] for k in ['name','entry_count','matched_entry_count','passed']} for x in record['checks']]},indent=2))
if not record['passed']:raise SystemExit(1)
