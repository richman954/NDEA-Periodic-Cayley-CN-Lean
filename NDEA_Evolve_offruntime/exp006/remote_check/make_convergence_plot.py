"""Numerical refinement figure for the concrete periodic mode, using Matplotlib."""
import cmath
import json
import math
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path('/content/exp006_check/convergence')
root.mkdir(exist_ok=True)
L=2*math.pi
T=L
rows=[]
for n in [8,16,32,64,128,256,512]:
    h=L/n
    k=h
    eigenvalue=4*math.sin(h/2)**2/h**2
    factor=lambda a:(1-1j*a*eigenvalue)/(1+1j*a*eigenvalue)
    numerical=(factor(k/4)**2*factor(k/2))**n
    exact=cmath.exp(-2j*T)
    error=math.sqrt(L)*abs(exact-numerical)
    bound=T*math.sqrt(L)*((5/16)*k*k+h*h/4)
    if error>bound+1e-10:
        raise RuntimeError('Numerical error exceeds the proposed bound')
    row={'n':n,'h':h,'k':k,'steps':n,'error':error,'bound':bound}
    if rows:row['observed_order']=math.log(rows[-1]['error']/error,2)
    rows.append(row)
fig,ax=plt.subplots(figsize=(8.8,5.8),layout='constrained')
ax.loglog([r['h'] for r in rows],[r['error'] for r in rows],'-o',color='#176b87',lw=2,label='Computed weighted error')
ax.loglog([r['h'] for r in rows],[r['bound'] for r in rows],'--',color='#b76529',lw=2,label='Explicit error bound')
ax.set_xlabel('Mesh spacing h = time step k')
ax.set_ylabel('Weighted error at T = 2π')
ax.set_title('Concrete periodic mode: second-order refinement',loc='left',fontsize=14,pad=16)
ax.grid(True,which='both',alpha=.2)
ax.legend(loc='upper left',frameon=False)
ax.text(.98,.05,f"Finest observed order: {rows[-1]['observed_order']:.4f}\n8–512 periodic grid points",
        transform=ax.transAxes,ha='right',va='bottom',fontsize=10)
fig.supxlabel('Floating-point diagnostic for U(t,x) = exp(i(x − 2t)); A = B = −∂xx',fontsize=10)
for ext in ['png','pdf','svg']:
    fig.savefig(root/f'exp006_convergence.{ext}',dpi=180)
(root/'refinement_data.json').write_text(json.dumps({'scope':'Floating-point diagnostic, not a theorem proof.',
                                                   'period':L,'horizon':T,'rows':rows},indent=2)+'\n')
print(json.dumps({'directory':str(root),'last_observed_order':rows[-1]['observed_order'],
                  'maximum_error_to_bound_ratio':max(r['error']/r['bound'] for r in rows)}))
