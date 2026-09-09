"""Independent floating-point checks of the infinite-series classical PDE.

The signed geometric coefficients have infinite support and an explicit finite
second weighted norm moment. Analytic derivative tails bound omitted modes in
exact arithmetic; neither these floats nor finite differences certify rounding.
This script does not repeat the predecessor's time-stepping diagnostics.
"""
import cmath
import datetime
import hashlib
import json
import math
from pathlib import Path


Q = 0.5
REFERENCE_RADIUS = 80
V_ZERO = (3 / 5 + 0j, 4j / 5)
V_PLUS = (3 / 5 + 0j, 4 / 5 + 0j)
V_MINUS = (4j / 5, 3 / 5 + 0j)
ZERO = (0j, 0j)
KINDS = ('value', 'time', 'space', 'second_space')


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def scale(c, v):
    return tuple(c * z for z in v)


def add(v, w):
    return tuple(x + y for x, y in zip(v, w))


def sub(v, w):
    return tuple(x - y for x, y in zip(v, w))


def norm(v):
    return math.sqrt(math.fsum(abs(z) ** 2 for z in v))


def sum_vectors(vectors):
    rows = list(vectors)
    return tuple(complex(math.fsum(v[j].real for v in rows),
                         math.fsum(v[j].imag for v in rows)) for j in range(2))


def potential(v):
    """(Z + X) v; the square of this matrix is 2 I."""
    return v[0] + v[1], v[0] - v[1]


def coefficient(m):
    if m == 0:
        return V_ZERO
    return scale((1j * Q) ** m, V_PLUS) if m > 0 else scale((-1j * Q) ** (-m), V_MINUS)


def mode_value(m, t, x):
    v = coefficient(m)
    theta = math.sqrt(2) * t
    rotated = add(scale(math.cos(theta), v),
                  scale(-1j * math.sin(theta) / math.sqrt(2), potential(v)))
    return scale(cmath.exp(1j * (m * x - m * m * t)), rotated)


def term(m, t, x, kind):
    u = mode_value(m, t, x)
    if kind == 'value':
        return u
    if kind == 'time':
        return scale(-1j, add(scale(m * m, u), potential(u)))
    if kind == 'space':
        return scale(1j * m, u)
    if kind == 'second_space':
        return scale(-m * m, u)
    raise ValueError(kind)


def reference(t, x, kind='value', radius=REFERENCE_RADIUS):
    return sum_vectors(term(m, t, x, kind) for m in range(-radius, radius + 1))


def moment_tail(radius, degree):
    """2 sum_{m=radius+1}^infinity m^degree Q^m for degree 0, 1, or 2.

    Expand m = n+j and use sum q^j, sum j q^j, sum j^2 q^j.
    These are analytic exact-real formulas evaluated here in binary floats.
    """
    n = radius + 1
    geometric = 1 / (1 - Q)
    first = Q / (1 - Q) ** 2
    second = Q * (1 + Q) / (1 - Q) ** 3
    polynomial = (geometric if degree == 0 else n * geometric + first
                  if degree == 1 else n * n * geometric + 2 * n * first + second)
    require(degree in (0, 1, 2), 'Unsupported moment degree')
    return 2 * Q ** n * polynomial


def derivative_tail(radius, kind):
    if kind == 'value':
        return moment_tail(radius, 0)
    if kind == 'space':
        return moment_tail(radius, 1)
    if kind == 'second_space':
        return moment_tail(radius, 2)
    if kind == 'time':
        # ||m^2 I + Z + X|| <= m^2 + 2, matching the proof's majorant.
        return moment_tail(radius, 2) + 2 * moment_tail(radius, 0)
    raise ValueError(kind)


def initial_closed(x, kind):
    """Closed sums at t=0 independently check the spatial derivatives."""
    p = 1j * Q * cmath.exp(1j * x)
    r = -1j * Q * cmath.exp(-1j * x)
    if kind == 'value':
        return add(V_ZERO, add(scale(p / (1 - p), V_PLUS), scale(r / (1 - r), V_MINUS)))
    if kind == 'space':
        return add(scale(1j * p / (1 - p) ** 2, V_PLUS),
                   scale(-1j * r / (1 - r) ** 2, V_MINUS))
    if kind == 'second_space':
        return add(scale(-p * (1 + p) / (1 - p) ** 3, V_PLUS),
                   scale(-r * (1 + r) / (1 - r) ** 3, V_MINUS))
    raise ValueError(kind)


def centered_difference(t, x, delta, kind):
    if kind == 'time':
        return scale(1 / (2 * delta), sub(reference(t + delta, x), reference(t - delta, x)))
    if kind == 'space':
        return scale(1 / (2 * delta), sub(reference(t, x + delta), reference(t, x - delta)))
    if kind == 'second_space':
        return scale(1 / delta ** 2, sub(add(reference(t, x + delta), reference(t, x - delta)),
                                        scale(2, reference(t, x))))
    raise ValueError(kind)


def main():
    root = Path(__file__).resolve().parent
    require(all(abs(norm(v) - 1) < 1e-15 for v in (V_ZERO, V_PLUS, V_MINUS)),
            'Geometric seed spinors must have unit norm')
    weighted_moment = 1 + moment_tail(0, 0) + 2 * moment_tail(0, 1) + moment_tail(0, 2)
    require(weighted_moment == 23, 'Second weighted moment formula mismatch')
    # Check the geometric moment identities against a separately summed prefix.
    moment_checks = []
    for radius in (0, 4, 8, 12, 20):
        for degree in (0, 1, 2):
            analytic = moment_tail(radius, degree)
            direct = 2 * math.fsum(m ** degree * Q ** m for m in range(radius + 1, 201))
            require(abs(analytic - direct) <= 5e-15 * analytic,
                    'Analytic omitted moment disagrees with direct geometric sum')
            moment_checks.append({'radius': radius, 'degree': degree, 'formula': analytic,
                                  'direct_sum_through_200': direct})
    points = [(t, x) for t in (-0.3, 0.0, 0.4) for x in (-1.2, 0.0, 0.7, math.pi)]
    deltas = [0.01 / 2 ** j for j in range(6)]
    rows, tails, differences, closed_checks = [], [], [], []
    for t, x in points:
        values = {kind: reference(t, x, kind) for kind in KINDS}
        # i U_t + U_xx - (Z+X)U = 0. Compare all derivative components together.
        pde_residual = norm(sub(add(scale(1j, values['time']), values['second_space']),
                                potential(values['value'])))
        periodic = max(norm(sub(reference(t, x + 2 * math.pi, kind), values[kind])) for kind in KINDS)
        wrong_time_sign = norm(sub(add(scale(-1j, values['time']), values['second_space']),
                                  potential(values['value'])))
        wrong_laplacian_sign = norm(sub(sub(scale(1j, values['time']), values['second_space']),
                                       potential(values['value'])))
        missing_potential = norm(add(scale(1j, values['time']), values['second_space']))
        require(pde_residual < 3e-13 and periodic < 4e-12,
                'Analytic derivative PDE or periodicity check failed')
        require(min(wrong_time_sign, wrong_laplacian_sign, missing_potential) > 0.01,
                'A sign or omitted-potential sensitivity control failed')
        rows.append({'t': t, 'x': x, 'analytic_pde_residual': pde_residual,
                     'maximum_periodicity_discrepancy': periodic,
                     'wrong_time_sign_residual': wrong_time_sign,
                     'wrong_laplacian_sign_residual': wrong_laplacian_sign,
                     'omitted_potential_residual': missing_potential})
        for kind in KINDS:
            for radius in (4, 8, 12, 20):
                discrepancy = norm(sub(reference(t, x, kind, radius), values[kind]))
                bound = derivative_tail(radius, kind)
                # Triangle inequality accounts for the reference's own omitted tail.
                upper = discrepancy + derivative_tail(REFERENCE_RADIUS, kind)
                require(upper <= bound + 2e-13,
                        'Observed derivative truncation exceeds its analytic tail bound')
                tails.append({'t': t, 'x': x, 'derivative': kind, 'cutoff': radius,
                              'computed_discrepancy': discrepancy,
                              'analytic_omitted_tail_bound': bound,
                              'discrepancy_plus_reference_tail': upper})
        for kind in KINDS[1:]:
            levels = []
            for delta in deltas:
                error = norm(sub(centered_difference(t, x, delta, kind), values[kind]))
                row = {'delta': delta, 'error': error}
                if levels:
                    row['observed_order'] = math.log2(levels[-1]['error'] / error)
                levels.append(row)
            require(all(b['error'] < a['error'] for a, b in zip(levels, levels[1:])),
                    'A centered derivative difference did not improve under refinement')
            require(1.9 < levels[-1]['observed_order'] < 2.1,
                    'A centered derivative difference lost second order')
            differences.append({'t': t, 'x': x, 'derivative': kind, 'levels': levels})
        if t == 0:
            for kind in ('value', 'space', 'second_space'):
                discrepancy = norm(sub(values[kind], initial_closed(x, kind)))
                require(discrepancy < 3e-14, 'Initial closed geometric derivative check failed')
                closed_checks.append({'x': x, 'derivative': kind, 'discrepancy': discrepancy})
    summary = {
        'pde_points': len(rows),
        'derivative_tail_cases': len(tails),
        'finite_difference_series': len(differences),
        'finite_difference_cases': sum(len(r['levels']) for r in differences),
        'closed_initial_cases': len(closed_checks),
        'geometric_moment_cases': len(moment_checks),
        'sign_and_potential_controls': 3 * len(rows),
        'maximum_analytic_pde_residual': max(r['analytic_pde_residual'] for r in rows),
        'maximum_periodicity_discrepancy': max(r['maximum_periodicity_discrepancy'] for r in rows),
        'minimum_finest_derivative_order': min(r['levels'][-1]['observed_order'] for r in differences),
        'maximum_finest_derivative_order': max(r['levels'][-1]['observed_order'] for r in differences),
        'maximum_derivative_tail_ratio': max(r['discrepancy_plus_reference_tail'] /
                                             r['analytic_omitted_tail_bound'] for r in tails),
        'minimum_wrong_model_residual': min(min(r[k] for k in
            ('wrong_time_sign_residual', 'wrong_laplacian_sign_residual', 'omitted_potential_residual'))
            for r in rows),
    }
    data = {
        'schema': 'ndea.exp010.classical-infinite-fourier-diagnostics.v1',
        'passed': True,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Supporting floating-point diagnostics of classical derivatives for one actual '
                 'infinite signed geometric datum. Exact-real omitted-tail formulas are evaluated '
                 'in ordinary floating point; these computations do not certify rounding or prove '
                 'the theorem. The formal encoded datum is a separate exact control.',
        'pde': 'i U_t = -U_xx + (Z + X) U',
        'datum': {'q': Q, 'a_0': '(3/5, 4i/5)',
                  'a_m_positive': '(i/2)^m (3/5, 4/5)',
                  'a_m_negative': '(-i/2)^(-m) (4i/5, 3/5)',
                  'support': 'all signed integers', 'coefficient_norm_mass': 3,
                  'second_weighted_norm_moment': weighted_moment},
        'reference': {'radius': REFERENCE_RADIUS,
                      'analytic_omitted_derivative_tails': {
                          kind: derivative_tail(REFERENCE_RADIUS, kind) for kind in KINDS}},
        'moment_formula_checks': moment_checks,
        'pde_and_sensitivity': rows,
        'derivative_tail_checks': tails,
        'finite_differences': differences,
        'initial_closed_form_checks': closed_checks,
        'summary': summary,
    }
    (root / 'evidence').mkdir(exist_ok=True)
    (root / 'evidence/numerical_checks.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'passed': True, **summary}, indent=2))


if __name__ == '__main__':
    main()
