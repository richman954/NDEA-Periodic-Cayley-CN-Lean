"""Finite-mode diagnostics in ordinary floating point; Lean carries the proof."""
import cmath,datetime,hashlib,json,math
from pathlib import Path

L=2*math.pi
IDENTITY=((1+0j,0j),(0j,1+0j))
X=((0j,1+0j),(1+0j,0j))
Z=((1+0j,0j),(0j,-1+0j))
def add(a,b):return tuple(tuple(a[i][j]+b[i][j] for j in range(2)) for i in range(2))
def scale(c,a):return tuple(tuple(c*a[i][j] for j in range(2)) for i in range(2))
def mm(a,b):return tuple(tuple(sum(a[i][r]*b[r][j] for r in range(2)) for j in range(2)) for i in range(2))
def mv(a,v):return tuple(sum(a[i][j]*v[j] for j in range(2)) for i in range(2))
def sub(v,w):return tuple(a-b for a,b in zip(v,w))
def vn(v):return math.sqrt(math.fsum(abs(x)**2 for x in v))
def inv(a):
    det=a[0][0]*a[1][1]-a[0][1]*a[1][0]
    return scale(1/det,((a[1][1],-a[0][1]),(-a[1][0],a[0][0])))
def power(a,n):
    result=IDENTITY
    while n:
        if n%2:result=mm(result,a)
        a=mm(a,a);n//=2
    return result
def cayley(a,t):return mm(add(IDENTITY,scale(-1j*t,a)),inv(add(IDENTITY,scale(1j*t,a))))
def step(lam,k,lie=False):
    a=add(scale(lam,IDENTITY),Z)
    if lie:return mm(cayley(X,k/2),cayley(a,k/2))
    c=cayley(a,k/4)
    return mm(mm(c,cayley(X,k/2)),c)
def orbit(m,t,v):
    internal=add(scale(math.cos(math.sqrt(2)*t),IDENTITY),
                 scale(-1j*math.sin(math.sqrt(2)*t)/math.sqrt(2),add(Z,X)))
    return tuple(cmath.exp(-1j*m*m*t)*w for w in mv(internal,v))
def symbol(m,h):return 4*math.sin(m*h/2)**2/h**2
def lift(d,coefficients):
    h=L/d
    return [tuple(sum(cmath.exp(1j*m*j*h)*v[a] for m,v in coefficients.items()) for a in range(2)) for j in range(d)]
def weightnorm(u,h):return math.sqrt(h*math.fsum(abs(x)**2 for row in u for x in row))
def difference(u,v):return [sub(a,b) for a,b in zip(u,v)]
def grid_a(u,h):
    d=len(u)
    return [tuple((2*u[j][a]-u[(j+1)%d][a]-u[(j-1)%d][a])/h**2+(1 if a==0 else -1)*u[j][a] for a in range(2)) for j in range(d)]
def grid_b(u,h):return [(v[1],v[0]) for v in u]
def residual(u,v,t,h,op):
    au,av=op(u,h),op(v,h)
    return [tuple(v[j][a]-u[j][a]+1j*t*(av[j][a]+au[j][a]) for a in range(2)) for j in range(len(u))]
def evolution(coefficients,t):return {m:orbit(m,t,v) for m,v in coefficients.items()}
def scheme(coefficients,h,k,N,lie=False,continuum_symbol=False):
    return {m:mv(power(step(m*m if continuum_symbol else symbol(m,h),k,lie),N),v) for m,v in coefficients.items()}
def order(rows):
    for p,q in zip(rows,rows[1:]):q['observed_order']=math.log(p['error']/q['error'],2)
    return rows
def require(ok,message):
    if not ok:raise RuntimeError(message)

def main():
    root=Path(__file__).resolve().parent
    raw={-2:(.2+.1j,.05j),0:(.3+0j,-.1j),1:(.5+0j,.2j),2:(.15j,.25+0j)}
    norm=math.sqrt(sum(vn(v)**2 for v in raw.values()))
    coeff={m:tuple(z/norm for z in v) for m,v in raw.items()}
    M=2;ct=1000*(M*M+2)**3;cs=M**4/8
    spectral_norm=math.sqrt(sum(vn(v)**2 for v in coeff.values()))
    stage_rows=[];global_rows=[];max_parseval=0;max_intertwining=0;max_first=0
    for d in (16,24,32,64,128):
        h=L/d
        require(d>2*M and M*h<=1,'Grid outside the intended hypotheses')
        for t in (0,.31,1):
            v=evolution(coeff,t);u=lift(d,v)
            max_parseval=max(max_parseval,abs(weightnorm(u,h)-math.sqrt(L)*spectral_norm))
            reduced_a={m:mv(add(scale(symbol(m,h),IDENTITY),Z),w) for m,w in v.items()}
            max_intertwining=max(max_intertwining,weightnorm(difference(grid_a(u,h),lift(d,reduced_a)),h))
            for k in (1/12,1/24,1/48,1/96):
                first={m:mv(cayley(add(scale(symbol(m,h),IDENTITY),Z),k/4),w) for m,w in v.items()}
                second={m:mv(cayley(X,k/2),w) for m,w in first.items()}
                f,s=lift(d,first),lift(d,second)
                r1=weightnorm(residual(u,f,k/4,h,grid_a),h)
                r2=weightnorm(residual(f,s,k/2,h,grid_b),h)
                r3=weightnorm(residual(s,lift(d,evolution(coeff,t+k)),k/4,h,grid_a),h)
                max_first=max(max_first,r1,r2)
                bound=(9/8)*math.sqrt(L)*k*(ct*k*k+cs*h*h)*spectral_norm
                require(r1+r2+r3<=bound+1e-9,'Actual stage budget exceeded target')
                stage_rows.append({'d':d,'t':t,'k':k,'first':r1,'second':r2,'third':r3,'budget':r1+r2+r3,'bound':bound})
        for N in (12,24,48,96):
            k=1/N
            error=weightnorm(difference(lift(d,scheme(coeff,h,k,N)),lift(d,evolution(coeff,1))),h)
            bound=math.sqrt(L)*(ct*k*k+cs*h*h)*spectral_norm
            require(error<=bound+1e-9,'Global error exceeded target')
            global_rows.append({'d':d,'N':N,'k':k,'h':h,'error':error,'bound':bound})
    joint=[]
    for d in (16,32,64,128,256,512,1024):
        h=L/d;k=1/d
        error=weightnorm(difference(lift(d,scheme(coeff,h,k,d)),lift(d,evolution(coeff,1))),h)
        joint.append({'d':d,'N':d,'h':h,'k':k,'error':error,'bound':math.sqrt(L)*(ct*k*k+cs*h*h)*spectral_norm})
    order(joint)
    temporal=[];lie=[]
    for N in (24,48,96,192,384,768):
        k=1/N
        for rows,is_lie in [(temporal,False),(lie,True)]:
            computed=scheme(coeff,L/32,k,N,lie=is_lie,continuum_symbol=True)
            error=math.sqrt(L*sum(vn(sub(computed[m],orbit(m,1,v)))**2 for m,v in coeff.items()))
            rows.append({'N':N,'k':k,'error':error})
    order(temporal);order(lie)
    require(joint[-1]['observed_order']>1.99 and temporal[-1]['observed_order']>1.99,'Second-order refinement not detected')
    require(.97<lie[-1]['observed_order']<1.03,'Lie sensitivity control did not detect first order')
    # Opposite coefficients at frequencies differing by d cancel on the grid.
    alias_d=8;alias={0:(1+0j,0j),alias_d:(-1+0j,0j)}
    alias_norm=weightnorm(lift(alias_d,alias),L/alias_d)
    false_parseval=math.sqrt(L*2)
    require(alias_norm<1e-12 and false_parseval>3,'Aliasing control failed')
    # An extra numerical mode is absorbed by e0, even outside the reference cutoff.
    d=32;h=L/d;N=48;k=1/N
    perturbed=dict(coeff);perturbed[5]=(.02+.01j,-.01j)
    e0=weightnorm(difference(lift(d,perturbed),lift(d,coeff)),h)
    eN=weightnorm(difference(lift(d,scheme(perturbed,h,k,N)),lift(d,evolution(coeff,1))),h)
    bound=e0+math.sqrt(L)*(ct*k*k+cs*h*h)*spectral_norm
    require(eN<=bound+1e-9,'Arbitrary initialization diagnostic failed')
    require(max_parseval<1e-11 and max_first<1e-9 and max_intertwining<1e-8,'Grid identity diagnostic failed')
    data={'schema':'ndea.exp008.finite-fourier-diagnostics.v1','passed':True,
          'scope':'Floating-point diagnostics only; no theorem proof. Fixed cutoff M=2.',
          'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'M':M,'frequencies':list(coeff),'coefficients':{str(m):[[z.real,z.imag] for z in v] for m,v in coeff.items()},
          'coefficient_l2_norm':spectral_norm,'Ct':ct,'Cs':cs,'stage_checks':stage_rows,'global_checks':global_rows,
          'joint_refinement':joint,'temporal_refinement':temporal,'lie_refinement':lie,
          'maximum_parseval_error':max_parseval,'maximum_wrapped_intertwining_error':max_intertwining,
          'maximum_first_two_residuals':max_first,
          'controls':{'alias_grid_norm':alias_norm,'invalid_parseval_prediction':false_parseval,'aliasing_detected':True,
                      'perturbed_initial_error':e0,'perturbed_final_error':eN,'perturbed_bound':bound}}
    (root/'evidence/numerical_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'passed':True,'stage_cases':len(stage_rows),'global_cases':len(global_rows),
                      'joint_order':joint[-1]['observed_order'],'temporal_order':temporal[-1]['observed_order'],
                      'lie_order':lie[-1]['observed_order'],'max_parseval_error':max_parseval,
                      'max_wrapped_intertwining_error':max_intertwining,'aliasing_detected':True},indent=2))
if __name__=='__main__':main()
