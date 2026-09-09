"""Supporting floating-point diagnostics; the Lean files carry the proofs."""
import cmath, datetime, hashlib, json, math
from pathlib import Path

L=2*math.pi
I=((1+0j,0j),(0j,1+0j))
X=((0j,1+0j),(1+0j,0j))
Z=((1+0j,0j),(0j,-1+0j))
v0=(1+0j,0j)
def add(a,b):return tuple(tuple(a[i][j]+b[i][j] for j in range(2)) for i in range(2))
def scale(c,a):return tuple(tuple(c*a[i][j] for j in range(2)) for i in range(2))
def mm(a,b):return tuple(tuple(sum(a[i][r]*b[r][j] for r in range(2)) for j in range(2)) for i in range(2))
def mv(a,v):return tuple(sum(a[i][j]*v[j] for j in range(2)) for i in range(2))
def sub(v,w):return tuple(a-b for a,b in zip(v,w))
def vn(v):return math.sqrt(math.fsum(abs(x)**2 for x in v))
def power(a,n):
    result=I
    while n:
        if n%2:result=mm(result,a)
        a=mm(a,a);n//=2
    return result
def inv(a):
    d=a[0][0]*a[1][1]-a[0][1]*a[1][0]
    return scale(1/d,((a[1][1],-a[0][1]),(-a[1][0],a[0][0])))
def cayley(a,alpha):return mm(add(I,scale(-1j*alpha,a)),inv(add(I,scale(1j*alpha,a))))
def step(lam,k,lie=False):
    a=add(scale(lam,I),Z)
    if lie:return mm(cayley(X,k/2),cayley(a,k/2))
    c=cayley(a,k/4)
    return mm(mm(c,cayley(X,k/2)),c)
def reference(t):
    c=math.cos(math.sqrt(2)*t);s=math.sin(math.sqrt(2)*t)/math.sqrt(2)
    return (cmath.exp(-1j*t)*(c-1j*s),cmath.exp(-1j*t)*(-1j*s))
def lift(n,v):
    h=L/n
    return [tuple(cmath.exp(1j*j*h)*x for x in v) for j in range(n)]
def grid_a(u,h):
    n=len(u)
    return [tuple((2*u[j][a]-u[(j+1)%n][a]-u[(j-1)%n][a])/h**2+(1 if a==0 else -1)*u[j][a] for a in range(2)) for j in range(n)]
def grid_b(u,h):return [(v[1],v[0]) for v in u]
def wn(u,h):return math.sqrt(h*math.fsum(abs(x)**2 for row in u for x in row))
def residual(s,t,alpha,h,op):
    hs,ht=op(s,h),op(t,h)
    return [tuple(t[j][a]-s[j][a]+1j*alpha*(ht[j][a]+hs[j][a]) for a in range(2)) for j in range(len(s))]
def order(rows):
    for previous,current in zip(rows,rows[1:]):current['observed_order']=math.log(previous['error']/current['error'],2)
    return rows
def main():
    stages=[];global_rows=[];max_intertwining=0;max_initial_residual=0
    for n in (7,8,16,32,64,128):
        h=L/n;lam=(2-2*math.cos(h))/h**2;a=add(scale(lam,I),Z)
        for t in (0,.37,1.25):
            v=reference(t);s=lift(n,v)
            max_intertwining=max(max_intertwining,max(vn(sub(p,q)) for p,q in zip(grid_a(s,h),lift(n,mv(a,v)))))
            for k in (1/6,1/12,1/24,1/48,1/96):
                first=mv(cayley(a,k/4),v);second=mv(cayley(X,k/2),first)
                r1=wn(residual(s,lift(n,first),k/4,h,grid_a),h)
                r2=wn(residual(lift(n,first),lift(n,second),k/2,h,grid_b),h)
                r3=wn(residual(lift(n,second),lift(n,reference(t+k)),k/4,h,grid_a),h)
                max_initial_residual=max(max_initial_residual,r1,r2)
                bound=math.sqrt(L)*k*(29250*k*k+13*h*h/96)
                assert r1+r2+r3<=bound+1e-10
                stages.append({'n':n,'t':t,'k':k,'budget':r1+r2+r3,'bound':bound})
        for N in (6,12,24,48,96):
            k=1/N
            numerical=mv(power(step(lam,k),N),v0)
            error=wn([sub(v,w) for v,w in zip(lift(n,numerical),lift(n,reference(1)))],h)
            bound=math.sqrt(L)*(27000*k*k+h*h/8)
            assert error<=bound+1e-10
            global_rows.append({'n':n,'N':N,'error':error,'bound':bound})
    joint=order([{'n':n,'N':n,'h':L/n,'k':1/n,'error':math.sqrt(L)*vn(sub(mv(power(step((2-2*math.cos(L/n))/(L/n)**2,1/n),n),v0),reference(1)))} for n in (8,16,32,64,128,256,512)])
    temporal=order([{'N':N,'k':1/N,'error':vn(sub(mv(power(step(1,1/N),N),v0),reference(1)))} for N in (12,24,48,96,192,384)])
    lie=order([{'N':N,'k':1/N,'error':vn(sub(mv(power(step(1,1/N,lie=True),N),v0),reference(1)))} for N in (12,24,48,96,192,384)])
    assert joint[-1]['observed_order']>1.99 and temporal[-1]['observed_order']>1.99
    assert .98<lie[-1]['observed_order']<1.02
    comm=vn(sub(mv(mm(add(I,Z),X),v0),mv(mm(X,add(I,Z)),v0)))
    assert abs(comm-2)<1e-12
    n=7;N=100000;k=1/N;h=L/n;lam=(2-2*math.cos(h))/h**2
    omitted_error=math.sqrt(L)*vn(sub(mv(power(step(lam,k),N),v0),reference(1)))
    temporal_only=math.sqrt(L)*27000*k*k
    assert omitted_error>temporal_only
    assert max_intertwining<1e-9 and max_initial_residual<1e-9
    data={'schema':'ndea.exp007.floating-point-diagnostics.v1','passed':True,
          'scope':'Supporting diagnostics only; not mathematical proof evidence.',
          'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'stage_checks':stages,'global_checks':global_rows,'joint_refinement':joint,
          'temporal_refinement':temporal,'lie_refinement':lie,
          'maximum_wrapped_intertwining_error':max_intertwining,
          'maximum_first_two_stage_residuals':max_initial_residual,
          'controls':{'commutator_witness_norm':comm,'lie_first_order_detected':True,
                      'omitted_spatial_term_rejected':True,'actual_error':omitted_error,'temporal_only_bound':temporal_only}}
    out=Path(__file__).parent/'evidence/numerical_checks.json'
    out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'passed':True,'stage_cases':len(stages),'global_cases':len(global_rows),'joint_order':joint[-1]['observed_order'],'temporal_order':temporal[-1]['observed_order'],'lie_order':lie[-1]['observed_order'],'maximum_wrapped_intertwining_error':max_intertwining},indent=2))
if __name__=='__main__':main()
