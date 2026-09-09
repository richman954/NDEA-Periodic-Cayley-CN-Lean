"""Render the saved finite-mode diagnostics using Matplotlib."""
from pathlib import Path
import hashlib,json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path('/content/exp008_check/diagnostics')
data=json.loads((root/'numerical_checks.json').read_text())
if data.get('passed') is not True:raise RuntimeError('Numerical diagnostics did not pass')
fig,axes=plt.subplots(1,2,figsize=(12.2,5.3),layout='constrained')
ax=axes[0];rows=data['joint_refinement']
ax.loglog([r['h'] for r in rows],[r['error'] for r in rows],'-o',color='#176b87',lw=2,label='Computed weighted error')
ax.loglog([r['h'] for r in rows],[r['bound'] for r in rows],'--',color='#b76529',lw=1.7,label='Explicit error bound')
ax.set_xlabel('Mesh spacing h (k = h / 2π)');ax.set_ylabel('Weighted error at T = 1')
ax.set_title('Joint spatial and temporal refinement',loc='left',fontsize=12)
ax.legend(frameon=False,fontsize=9)
ax.text(.98,.05,f"Finest observed order: {rows[-1]['observed_order']:.6f}",transform=ax.transAxes,ha='right',fontsize=9)
ax=axes[1]
for key,label,color in [('temporal_refinement','Symmetric Cayley','#176b87'),('lie_refinement','Unsymmetric Lie control','#b76529')]:
    rs=data[key]
    ax.loglog([r['k'] for r in rs],[r['error'] for r in rs],'-o',lw=2,color=color,label=f"{label} (order {rs[-1]['observed_order']:.4f})")
ax.set_xlabel('Time step k');ax.set_ylabel('Weighted error with continuum symbols')
ax.set_title('Temporal order and sensitivity control',loc='left',fontsize=12)
ax.legend(frameon=False,fontsize=9)
for ax in axes:ax.grid(True,which='both',alpha=.18)
fig.suptitle('Experiment 008: a finite superposition of noncommuting spinor modes',x=.01,ha='left',fontsize=14)
fig.supxlabel('Frequencies −2, 0, 1, 2 • coefficient norm 1 • floating-point diagnostics, separate from Lean proofs',fontsize=10)
files={}
for ext in ['png','pdf','svg']:
    path=root/('exp008_convergence.'+ext);fig.savefig(path,dpi=180)
    files[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
(root/'FIGURE_RECEIPT.json').write_text(json.dumps({'files':files,'data_sha256':hashlib.sha256((root/'numerical_checks.json').read_bytes()).hexdigest()},indent=2)+'\n')
print(json.dumps({'directory':str(root),'files':list(files)}))
