import pathlib,json,math,hashlib
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
r=pathlib.Path('/content/exp007_check/diagnostics');r.mkdir(exist_ok=True)
(r/'numerical_checks.json').write_bytes(pathlib.Path('/content/exp007_numerical_checks.json').read_bytes())
data=json.loads((r/'numerical_checks.json').read_text())
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(10.8,4.0))
rows=data['joint_refinement'];x=[v['h'] for v in rows];y=[v['error'] for v in rows]
axes[0].loglog(x,y,'o-',color='#1967a0',label='Actual weighted grid error')
axes[0].loglog(x,[y[-1]*(z/x[-1])**2 for z in x],'--',color='#999999',label='Second-order guide')
axes[0].set(xlabel='Spatial mesh h = 2π/d',ylabel='Error at T = 1',title='Joint mesh refinement: k = 1/d')
for key,label,col in [('temporal_refinement','Symmetric Cayley','#1967a0'),('lie_refinement','Nonsymmetric control','#bd5a2b')]:
 rows=data[key];axes[1].loglog([v['k'] for v in rows],[v['error'] for v in rows],'o-',color=col,label=label)
axes[1].set(xlabel='Time step k',ylabel='Reduced spinor error at T = 1',title='Time error: exact spatial symbol λ = 1')
for ax in axes:ax.grid(True,which='both',alpha=.18);ax.legend(frameon=False,fontsize=8)
fig.suptitle('Experiment 007: noncommuting periodic spinor equation',fontsize=13)
fig.tight_layout()
for ext in ['png','pdf','svg']:fig.savefig(r/('exp007_convergence.'+ext),dpi=180,bbox_inches='tight')
print(json.dumps({'generated':[str(p) for p in r.glob('exp007_convergence.*')],'qualification':'Floating-point diagnostics; formal proof is separate.'}))
