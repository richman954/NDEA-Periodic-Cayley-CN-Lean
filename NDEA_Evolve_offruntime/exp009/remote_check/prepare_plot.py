from pathlib import Path
import json
import matplotlib

root = Path('/content/exp009_check/plots')
root.mkdir(parents=True, exist_ok=True)
print(json.dumps({'directory': str(root), 'matplotlib_version': matplotlib.__version__}))
