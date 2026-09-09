import pathlib, json
r=pathlib.Path('/content/exp007_check/development')
for name in ['ReducedNoncommuting','ReducedClosure']:
 result=r/('model_'+name+'_RESULT.json');log=r/('model_'+name+'.log')
 print(name, result.read_text() if result.exists() else 'RUNNING_OR_PENDING')
 if log.exists():print(log.read_text()[-12000:])
