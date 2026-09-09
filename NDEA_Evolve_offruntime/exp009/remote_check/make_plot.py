"""Render and package the accepted numerical refinement figure on Colab."""
import hashlib, json, runpy, sys, tarfile
from pathlib import Path
root=Path('/content/exp009_check')
sys.argv=[str(root/'plot_convergence.py'),'--input',str(root/'numerical_checks.json'),
    '--sha256','b9d09e60db3e49a829bf94871fedb4ae9c8ba66bc59b0f49173c8d57ee7d1c3f',
    '--output',str(root/'plots')]
runpy.run_path(sys.argv[0],run_name='__main__')
archive=root/'convergence_plot.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for p in sorted((root/'plots').iterdir()):tar.add(p,arcname=p.name,recursive=False)
print(json.dumps({'archive':str(archive),'sha256':hashlib.sha256(archive.read_bytes()).hexdigest()}))
