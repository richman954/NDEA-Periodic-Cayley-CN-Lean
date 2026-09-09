"""Floating-point diagnostics of actual wrapped-grid factors; not proof evidence."""
import cmath
import datetime
import hashlib
import json
import math
from pathlib import Path

L = 2 * math.pi


def mode(n, phase):
    h = L / n
    return [cmath.exp(1j * (j * h - phase)) for j in range(n)]


def laplacian(u, h):
    n = len(u)
    return [(2 * u[j] - u[(j + 1) % n] - u[(j - 1) % n]) / h**2
            for j in range(n)]


def factor_residual(source, target, alpha, h, sign=1):
    hs, ht = laplacian(source, h), laplacian(target, h)
    return [t - s + sign * 1j * alpha * (a + b)
            for s, t, a, b in zip(source, target, hs, ht)]


def weighted_norm(u, h):
    return math.sqrt(h * math.fsum(abs(z)**2 for z in u))


def budget(n, k, phase=0, sign=1):
    h = L / n
    states = [mode(n, phase + shift) for shift in (0, k/2, 3*k/2, 2*k)]
    return sum(weighted_norm(factor_residual(states[j], states[j+1], a, h, sign), h)
               for j, a in enumerate((k/4, k/2, k/4)))


def main():
    rows, global_rows = [], []
    maximum_symbol_error = 0
    for n in (7, 8, 12, 16, 32, 64, 128):
        h = L/n
        eigenvalue = (2 - 2*math.cos(h))/h**2
        u = mode(n, 0.37)
        maximum_symbol_error = max(maximum_symbol_error,
            max(abs(a-eigenvalue*b) for a,b in zip(laplacian(u,h),u)))
        if abs(eigenvalue-1) > h*h/8 + 1e-12:
            raise RuntimeError('Spatial estimate failed')
        for k in (2.0, 1.0, 0.5, 0.25, 0.1, 0.05, 0.01):
            bound = math.sqrt(L)*k*((5/16)*k*k + h*h/4)
            for phase in (0, 0.74, 4.0):
                observed = budget(n,k,phase)
                rows.append({'n':n,'h':h,'k':k,'phase':phase,'budget':observed,
                             'bound':bound,'ratio':observed/bound})
                if observed > bound + 1e-11:
                    raise RuntimeError('Stage residual estimate failed')
            # The matrix is circulant. Its sampled mode eigenvalue is also
            # checked directly above with wrapped neighbor accesses.
            def cayley(alpha):
                return (1-1j*alpha*eigenvalue)/(1+1j*alpha*eigenvalue)
            step = cayley(k/4)*cayley(k/2)*cayley(k/4)
            steps = int(4/k)
            horizon = steps*k
            numerical = [step**steps*z for z in mode(n,0)]
            exact = mode(n,2*horizon)
            error = weighted_norm([a-b for a,b in zip(exact,numerical)],h)
            bound = math.sqrt(L)*horizon*((5/16)*k*k+h*h/4)
            global_rows.append({'n':n,'k':k,'steps':steps,'horizon':horizon,
                                'error':error,'bound':bound,'ratio':error/bound})
            if error > bound + 1e-10:
                raise RuntimeError('Global error diagnostic failed')
    if maximum_symbol_error > 1e-9:
        raise RuntimeError('Wrapped stencil disagrees with Fourier symbol')
    n,k=128,0.01
    wrong_sign=budget(n,k,sign=-1)
    valid_bound=math.sqrt(L)*k*((5/16)*k*k+(L/n)**2/4)
    n2=7
    actual=budget(n2,k)
    omitted_space_bound=math.sqrt(L)*k*(5/16)*k*k
    if not (wrong_sign > valid_bound and actual > omitted_space_bound):
        raise RuntimeError('Expected sensitivity controls did not reject')
    report={'schema':'ndea.exp006.floating-point-diagnostics.v1',
        'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Supporting floating-point checks only; no theorem proved by this script.',
        'pde':'i U_t = -2 U_xx; U(t,x)=exp(i(x-2t)); A=B=negative centered second difference',
        'period':L,'stage_checks':rows,'global_checks':global_rows,
        'maximum_wrapped_symbol_error':maximum_symbol_error,
        'worst_stage_ratio':max(r['ratio'] for r in rows),
        'worst_global_ratio':max(r['ratio'] for r in global_rows),
        'controls':{'wrong_factor_sign_rejected':True,'wrong_sign_budget':wrong_sign,
                    'correct_bound':valid_bound,'omitted_spatial_term_rejected':True,
                    'coarse_grid_budget':actual,'temporal_only_bound':omitted_space_bound},
        'passed':True}
    output=Path(__file__).parent/'evidence/numerical_checks.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('passed','worst_stage_ratio','worst_global_ratio',
                                         'maximum_wrapped_symbol_error')}))
    print('stage_cases',len(rows),'global_cases',len(global_rows),'result',output)


if __name__=='__main__':
    main()
