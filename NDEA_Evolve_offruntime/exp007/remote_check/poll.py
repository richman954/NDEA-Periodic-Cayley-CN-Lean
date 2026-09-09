import pathlib,json
root=pathlib.Path('/content/exp007_check')
p=root/'bootstrap/RESULT.json'
if p.exists():
 d=json.loads(p.read_text());print(json.dumps({k:d.get(k) for k in ['passed','error','start_utc','end_utc']}));print(json.dumps(d.get('commands',[])[-1:]))
print((root/'bootstrap_controller.log').read_text()[-1200:])
