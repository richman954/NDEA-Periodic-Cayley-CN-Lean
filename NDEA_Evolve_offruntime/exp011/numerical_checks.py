"""Focused floating-point checks of the explicit space-time reconstruction.

The datum is an infinite signed geometric Fourier series. Initial samples use
closed geometric sums, reference values use a finite sum with an analytic
omitted-tail bound, and bin indices use exact rational grid coordinates.
No computation here certifies floating-point rounding or replaces Lean.
"""
import cmath
import datetime
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path


L = 2 * math.pi
Q = 0.5
RADIUS = 80
MOMENT_TWO = 23.0
ZERO = (0j, 0j)
V_ZERO = (3 / 5 + 0j, 4j / 5)
V_PLUS = (3 / 5 + 0j, 4 / 5 + 0j)
V_MINUS = (4j / 5, 3 / 5 + 0j)
IDENTITY = ((1 + 0j, 0j), (0j, 1 + 0j))
Z = ((1 + 0j, 0j), (0j, -1 + 0j))
X = ((0j, 1 + 0j), (1 + 0j, 0j))


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def add(v, w):
    return tuple(a + b for a, b in zip(v, w))


def sub(v, w):
    return tuple(a - b for a, b in zip(v, w))


def scale(c, v):
    return tuple(c * a for a in v)


def norm(v):
    return math.sqrt(math.fsum(abs(a) ** 2 for a in v))


def sum_vectors(rows):
    rows = list(rows)
    return tuple(complex(math.fsum(v[b].real for v in rows),
                         math.fsum(v[b].imag for v in rows)) for b in range(2))


def mat_add(a, b):
    return tuple(tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2))


def mat_scale(c, a):
    return tuple(tuple(c * a[i][j] for j in range(2)) for i in range(2))


def mat_mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def mat_vec(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(2)) for i in range(2))


def mat_inv(a):
    d = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    return mat_scale(1 / d, ((a[1][1], -a[0][1]), (-a[1][0], a[0][0])))


def mat_pow(a, n):
    answer = IDENTITY
    while n:
        if n % 2:
            answer = mat_mul(answer, a)
        a = mat_mul(a, a)
        n //= 2
    return answer


def cayley(a, alpha):
    return mat_mul(mat_add(IDENTITY, mat_scale(-1j * alpha, a)),
                   mat_inv(mat_add(IDENTITY, mat_scale(1j * alpha, a))))


def split_step(lam, k):
    first = cayley(mat_add(mat_scale(lam, IDENTITY), Z), k / 4)
    return mat_mul(mat_mul(first, cayley(X, k / 2)), first)


def coefficient(m):
    if m == 0:
        return V_ZERO
    return scale((1j * Q) ** m, V_PLUS) if m > 0 else scale((-1j * Q) ** (-m), V_MINUS)


def orbit(m, t, v):
    theta = math.sqrt(2) * t
    rotated = add(scale(math.cos(theta), v),
                  scale(-1j * math.sin(theta) / math.sqrt(2), (v[0] + v[1], v[0] - v[1])))
    return scale(cmath.exp(-1j * m * m * t), rotated)


def reference(t, x, radius=RADIUS):
    return sum_vectors(scale(cmath.exp(1j * m * x), orbit(m, t, coefficient(m)))
                       for m in range(-radius, radius + 1))


def reference_tail(radius=RADIUS):
    """Exact-real upper bound for the omitted pointwise spinor series."""
    return 2 * Q ** (radius + 1) / (1 - Q)


def initial_value(x):
    p, r = 1j * Q * cmath.exp(1j * x), -1j * Q * cmath.exp(-1j * x)
    return add(V_ZERO, add(scale(p / (1 - p), V_PLUS), scale(r / (1 - r), V_MINUS)))


def initial_aliases(d):
    answer = []
    p, r = 1j * Q, -1j * Q
    for j in range(d):
        vp = scale(p ** (j if j else d) / (1 - p ** d), V_PLUS)
        vm = scale(r ** (d - j if j else d) / (1 - r ** d), V_MINUS)
        answer.append(add(add(vp, vm), V_ZERO if j == 0 else ZERO))
    return answer


def evolve_aliases(initial, d, k, count):
    h = L / d
    rows = []
    for r, v in enumerate(initial):
        m = r if r <= d // 2 else r - d
        lam = 4 * math.sin(m * h / 2) ** 2 / h ** 2
        rows.append(mat_vec(mat_pow(split_step(lam, k), count), v) if v != ZERO else ZERO)
    return rows


def node_value(bins, d, j):
    return sum_vectors(scale(cmath.exp(2j * math.pi * (r if r <= d // 2 else r - d) * j / d), v)
                       for r, v in enumerate(bins) if v != ZERO)


def reference_aliases(d, t):
    rows = [ZERO for _ in range(d)]
    for m in range(-RADIUS, RADIUS + 1):
        rows[m % d] = add(rows[m % d], orbit(m, t, coefficient(m)))
    return rows


def space_index(d, position):
    """position=x/(2π); exact rational indexing matches the formal clamp."""
    z = position * d
    return min(z.numerator // z.denominator, d - 1)


def time_index(count, time):
    """k=1/count, time rational in [0,1], so endpoint classification is exact."""
    z = time * count
    return min(z.numerator // z.denominator, count)


def solve(a, b):
    """Dense complex Gaussian elimination, used only for small-grid cross-checks."""
    n = len(b)
    a = [list(row) + [b[i]] for i, row in enumerate(a)]
    for j in range(n):
        p = max(range(j, n), key=lambda i: abs(a[i][j]))
        require(abs(a[p][j]) > 1e-14, 'Dense Cayley system appears singular')
        a[j], a[p] = a[p], a[j]
        pivot = a[j][j]
        a[j] = [z / pivot for z in a[j]]
        for i in range(n):
            if i != j:
                factor = a[i][j]
                a[i] = [x - factor * y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def dense_cayley(generator, alpha, v):
    n = len(v)
    left = [[(1 if i == j else 0) + 1j * alpha * generator[i][j]
             for j in range(n)] for i in range(n)]
    right = [v[i] - 1j * alpha * sum(generator[i][j] * v[j] for j in range(n))
             for i in range(n)]
    return solve(left, right)


def dense_check(d, count):
    h, k = L / d, 1 / count
    size = 2 * d
    a, b = [[0j] * size for _ in range(size)], [[0j] * size for _ in range(size)]
    for j in range(d):
        for spin in range(2):
            row = 2 * j + spin
            a[row][row] = 2 / h ** 2 + (1 if spin == 0 else -1)
            a[row][2 * ((j + 1) % d) + spin] -= 1 / h ** 2
            a[row][2 * ((j - 1) % d) + spin] -= 1 / h ** 2
            b[row][2 * j + 1 - spin] = 1
    initial = initial_aliases(d)
    state = [z for j in range(d) for z in initial_value(j * h)]
    checks = []
    for step in range(4):
        if step:
            state = dense_cayley(a, k / 4, state)
            state = dense_cayley(b, k / 2, state)
            state = dense_cayley(a, k / 4, state)
        bins = evolve_aliases(initial, d, k, step)
        discrepancy = max(norm(sub(tuple(state[2*j:2*j+2]), node_value(bins, d, j))) for j in range(d))
        require(discrepancy < 2e-11, 'Reconstructed node differs from direct full-spinor Cayley state')
        for position in (Fraction(0), Fraction(7, 3*d), Fraction(d-1, d), Fraction(1)):
            index = space_index(d, position)
            actual = tuple(state[2*index:2*index+2])
            require(norm(sub(actual, node_value(bins, d, index))) < 2e-11,
                    'Off-grid block extraction disagrees with direct matrix state')
        checks.append({'step': step, 'maximum_node_discrepancy': discrepancy})
    return {'grid_points': d, 'time_step': k, 'node_checks': d * len(checks),
            'off_grid_extraction_checks': 4 * len(checks), 'steps': checks}


def main():
    root = Path(__file__).resolve().parent
    require(all(abs(norm(v) - 1) < 1e-15 for v in (V_ZERO, V_PLUS, V_MINUS)),
            'The geometric seed spinors must have unit norm')
    geometric_moment = 1 + 2 * (Q / (1-Q) + 2*Q / (1-Q)**2 + Q*(1+Q) / (1-Q)**3)
    require(MOMENT_TWO == geometric_moment, 'Second weighted moment formula mismatch')
    dense = [dense_check(8, 6), dense_check(16, 24)]
    levels, cases, index_cases, controls = [], [], [], []
    fixed_times = [Fraction(0), Fraction(1, 97), Fraction(2, 7), Fraction(1, 2), Fraction(11, 13), Fraction(1)]
    fixed_positions = [Fraction(j, 12) for j in range(13)] + [Fraction(1, 97), Fraction(2, 7), Fraction(11, 13)]
    for cutoff in (1, 2, 4, 8):
        d, count = 8 * cutoff ** 3, 6 * cutoff ** 4
        h, k = L / d, 1 / count
        initial = initial_aliases(d)
        times = fixed_times + [Fraction(5, 4 * count)]
        positions = fixed_positions + [Fraction(7, 3 * d)]
        coefficient_bound = (1000 / 36) * (1 + 2 / cutoff ** 2) ** 3 + math.pi ** 2 / 128 + 2
        nodal_bound = MOMENT_TWO * coefficient_bound * math.sqrt(8 / cutoff)
        uniform_bound = nodal_bound + MOMENT_TWO * h + 2 * MOMENT_TWO * k
        local_rows = []
        for time in times:
            j = time_index(count, time)
            lag = time - Fraction(j, count)
            require(0 <= lag <= Fraction(1, count), 'Clamped time index exceeds one-step lag')
            t, s = float(time), j * k
            bins = evolve_aliases(initial, d, k, j)
            refs = reference_aliases(d, s)
            # Finite alias bins only: this is an ordinary finite discrete norm identity.
            measured_grid_error = math.sqrt(L * math.fsum(norm(sub(v, w)) ** 2 for v, w in zip(bins, refs)))
            full_nodal_bound = (measured_grid_error + math.sqrt(L) * reference_tail()) / math.sqrt(h)
            require(full_nodal_bound <= nodal_bound + 2e-10, 'Computed nodal bound exceeds formal envelope')
            for position in positions:
                i = space_index(d, position)
                gap = position - Fraction(i, d)
                require(0 <= gap <= Fraction(1, d), 'Clamped spatial index exceeds one-cell distance')
                x, y = float(position) * L, i * h
                value = node_value(bins, d, i)
                node_reference, space_reference, target = reference(s, y), reference(s, x), reference(t, x)
                error = norm(sub(value, target))
                nodal_error = norm(sub(value, node_reference))
                spatial_error = norm(sub(node_reference, space_reference))
                temporal_error = norm(sub(space_reference, target))
                require(nodal_error <= full_nodal_bound + reference_tail() + 2e-10,
                        'Node extraction exceeds full-grid norm estimate')
                require(spatial_error <= MOMENT_TWO * abs(y-x) + 2e-12,
                        'Spatial quantization exceeds derivative moment bound')
                require(temporal_error <= 2 * MOMENT_TWO * abs(s-t) + 2e-12,
                        'Temporal quantization exceeds derivative moment bound')
                require(error <= nodal_error + spatial_error + temporal_error + 2e-12,
                        'Reconstruction error decomposition failed')
                require(error + reference_tail() <= uniform_bound + 2e-10,
                        'Off-grid error exceeds theorem envelope')
                row = {'cutoff': cutoff, 'time': str(time), 'position_fraction_of_period': str(position),
                       'time_index': j, 'space_index': i, 'time_lag': float(lag),
                       'space_gap': float(gap) * L, 'error_to_radius_80_reference': error,
                       'reference_omitted_tail_bound': reference_tail(),
                       'nodal_error_to_finite_reference': nodal_error, 'spatial_quantization_error': spatial_error,
                       'temporal_quantization_error': temporal_error, 'uniform_theorem_envelope': uniform_bound}
                cases.append(row)
                local_rows.append(row)
        require(space_index(d, Fraction(1)) == d - 1 and space_index(d, Fraction(0)) == 0,
                'Spatial endpoint clamp changed')
        require(time_index(count, Fraction(1)) == count and time_index(count, Fraction(0)) == 0,
                'Temporal endpoint clamp changed')
        endpoint_difference = norm(sub(initial_value((d-1)*h), initial_value(0)))
        require(endpoint_difference > 1e-6, 'Endpoint control cannot distinguish clamp from wrapping')
        index_cases.append({'cutoff': cutoff, 'right_space_index': d-1, 'terminal_time_index': count,
                            'initial_last_vs_first_node_difference': endpoint_difference})
        wrong_time = Fraction(5, 4 * count)
        right_bins, next_bins = evolve_aliases(initial, d, k, 1), evolve_aliases(initial, d, k, 2)
        wrong_space = norm(sub(node_value(right_bins, d, 3), node_value(right_bins, d, 2)))
        wrong_step = norm(sub(node_value(next_bins, d, 2), node_value(right_bins, d, 2)))
        require(space_index(d, Fraction(7, 3*d)) == 2 and time_index(count, wrong_time) == 1,
                'Interior exact rational floor control failed')
        require(wrong_space > 1e-7 and wrong_step > 1e-7, 'Wrong-index sensitivity control is ineffective')
        controls.append({'cutoff': cutoff, 'next_spatial_node_discrepancy': wrong_space,
                         'next_time_step_discrepancy': wrong_step})
        largest = max(row['error_to_radius_80_reference'] for row in local_rows)
        level = {'cutoff': cutoff, 'grid_points': d, 'steps': count, 'h': h, 'k': k,
                 'sampled_off_grid_points': len(local_rows), 'maximum_sampled_error': largest,
                 'nodal_theorem_envelope': nodal_bound, 'uniform_theorem_envelope': uniform_bound}
        if levels:
            level['observed_order_in_cutoff'] = math.log2(levels[-1]['maximum_sampled_error'] / largest)
            level['observed_order_in_mesh'] = level['observed_order_in_cutoff'] / 3
        levels.append(level)
    require(levels[-1]['maximum_sampled_error'] < 0.05 * levels[0]['maximum_sampled_error'],
            'Off-grid errors did not decrease substantially on the scheduled refinement')
    summary = {'refinement_levels': len(levels), 'off_grid_cases': len(cases),
               'dense_full_spinor_node_checks': sum(row['node_checks'] for row in dense),
               'dense_off_grid_extraction_checks': sum(row['off_grid_extraction_checks'] for row in dense),
               'endpoint_pairs': len(index_cases), 'wrong_index_controls': 2 * len(controls),
               'finest_maximum_sampled_error': levels[-1]['maximum_sampled_error'],
               'finest_observed_order_in_cutoff': levels[-1]['observed_order_in_cutoff'],
               'finest_observed_order_in_mesh': levels[-1]['observed_order_in_mesh'],
               'maximum_dense_discrepancy': max(s['maximum_node_discrepancy'] for row in dense for s in row['steps']),
               'analytic_reference_tail': reference_tail()}
    data = {'schema': 'ndea.exp011.off-grid-reconstruction-diagnostics.v1', 'passed': True,
            'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope': 'Supporting ordinary floating-point reconstruction diagnostics. Exact-real '
                     'geometric truncation bounds do not certify roundoff. Finite test points do '
                     'not prove a uniform supremum estimate; the separate Lean theorem does.',
            'datum': {'q': Q, 'a0': '(3/5,4i/5)', 'positive': '(i/2)^m*(3/5,4/5)',
                      'negative': '(-i/2)^abs(m)*(4i/5,3/5)', 'second_weighted_moment': MOMENT_TWO,
                      'reference_radius': RADIUS},
            'index_semantics': 'Exact rational fractions of period/time horizon; spatial right '
                               'endpoint clamps to last node, terminal time uses final step. '
                               'The reconstructed field is defined on the closed rectangle and '
                               'is not required to agree at its spatial endpoints.',
            'summary': summary, 'levels': levels, 'off_grid_cases': cases, 'dense_checks': dense,
            'endpoint_controls': index_cases, 'wrong_index_controls': controls}
    (root / 'evidence').mkdir(exist_ok=True)
    (root / 'evidence/numerical_checks.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'passed': True, 'summary': summary}))


if __name__ == '__main__':
    main()
