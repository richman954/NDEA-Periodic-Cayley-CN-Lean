import pathlib
r=pathlib.Path('/content/exp007_check/development')
p=r/'FOUNDATION_RESULT.json'
print(p.read_text() if p.exists() else 'FOUNDATION_RUNNING')
print((r/'foundation.log').read_text()[-1000:])
