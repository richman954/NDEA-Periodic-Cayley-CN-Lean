"""Infinite-data diagnostics in floating point; these calculations are not proofs.

The datum is an actual infinite geometric Fourier series. Its sampled initial
state is evaluated by closed geometric alias sums, while the terminal reference
uses a finite sum with a stated analytic bound on its omitted tail. The tail
bound concerns truncation in exact arithmetic, not floating-point roundoff.
Only finite alias bins use discrete Fourier orthogonality below; no infinite
Parseval identity or l2-to-sampling estimate is assumed.
"""
import cmath
import datetime
import hashlib
import json
import math
from pathlib import Path


L = 2 * math.pi
Q = 0.5
REFERENCE_RADIUS = 48
IDENTITY = ((1 + 0j, 0j), (0j, 1 + 0j))
X = ((0j, 1 + 0j), (1 + 0j, 0j))
Z = ((1 + 0j, 0j), (0j, -1 + 0j))
V_ZERO = (3 / 5 + 0j, 4j / 5)
V_PLUS = (3 / 5 + 0j, 4 / 5 + 0j)
V_MINUS = (4j / 5, 3 / 5 + 0j)
ZERO = (0j, 0j)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def matrix_add(a, b):
    return tuple(tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2))


def matrix_scale(c, a):
    return tuple(tuple(c * a[i][j] for j in range(2)) for i in range(2))


def matrix_product(a, b):
    return tuple(tuple(sum(a[i][r] * b[r][j] for r in range(2))
                       for j in range(2)) for i in range(2))


def matrix_vector(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(2)) for i in range(2))


def vector_scale(c, v):
    return tuple(c * x for x in v)


def vector_add(v, w):
    return tuple(x + y for x, y in zip(v, w))


def vector_sub(v, w):
    return tuple(x - y for x, y in zip(v, w))


def vector_norm(v):
    return math.sqrt(math.fsum(abs(x) ** 2 for x in v))


def inverse(a):
    det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    return matrix_scale(1 / det, ((a[1][1], -a[0][1]), (-a[1][0], a[0][0])))


def matrix_power(a, n):
    result = IDENTITY
    while n:
        if n % 2:
            result = matrix_product(result, a)
        a = matrix_product(a, a)
        n //= 2
    return result


def cayley(a, alpha):
    return matrix_product(matrix_add(IDENTITY, matrix_scale(-1j * alpha, a)),
                          inverse(matrix_add(IDENTITY, matrix_scale(1j * alpha, a))))


def step(lam, k):
    a = matrix_add(matrix_scale(lam, IDENTITY), Z)
    c = cayley(a, k / 4)
    return matrix_product(matrix_product(c, cayley(X, k / 2)), c)


def symbol(r, d):
    # The signed representative avoids loss of precision near 2*pi.
    m = r if r <= d // 2 else r - d
    h = L / d
    return 4 * math.sin(m * h / 2) ** 2 / h ** 2


def coefficient(m):
    if m == 0:
        return V_ZERO
    if m > 0:
        return vector_scale((1j * Q) ** m, V_PLUS)
    return vector_scale((-1j * Q) ** (-m), V_MINUS)


def orbit(m, t, v):
    internal = matrix_add(matrix_scale(math.cos(math.sqrt(2) * t), IDENTITY),
                          matrix_scale(-1j * math.sin(math.sqrt(2) * t) / math.sqrt(2),
                                       matrix_add(Z, X)))
    return vector_scale(cmath.exp(-1j * m * m * t), matrix_vector(internal, v))


def coefficient_mass():
    return 1 + 2 * Q / (1 - Q)


def coefficient_tail(radius):
    """Exact real formula for sum_{|m|>radius} ||a_m||_2."""
    return 2 * Q ** (radius + 1) / (1 - Q)


def exact_initial_aliases(d):
    """Closed geometric sums for every congruence class of the full series."""
    plus, minus = 1j * Q, -1j * Q
    answer = []
    for r in range(d):
        first_positive = r if r else d
        first_negative = d - r if r else d
        positive = plus ** first_positive / (1 - plus ** d)
        negative = minus ** first_negative / (1 - minus ** d)
        v = vector_add(vector_scale(positive, V_PLUS), vector_scale(negative, V_MINUS))
        answer.append(vector_add(v, V_ZERO) if r == 0 else v)
    return answer


def exact_initial_value(x):
    plus, minus = 1j * Q * cmath.exp(1j * x), -1j * Q * cmath.exp(-1j * x)
    return vector_add(V_ZERO, vector_add(vector_scale(plus / (1 - plus), V_PLUS),
                                         vector_scale(minus / (1 - minus), V_MINUS)))


def finite_reference_aliases(d, radius, t):
    bins = [ZERO for _ in range(d)]
    for m in range(-radius, radius + 1):
        bins[m % d] = vector_add(bins[m % d], orbit(m, t, coefficient(m)))
    return bins


def alias_difference(a, b):
    return [vector_sub(v, w) for v, w in zip(a, b)]


def alias_weighted_norm(bins):
    # This is finite discrete orthogonality after alias contributions are summed.
    return math.sqrt(L * math.fsum(abs(x) ** 2 for v in bins for x in v))


def evolve_grid_aliases(bins, d, k, n):
    return [matrix_vector(matrix_power(step(symbol(r, d), k), n), v)
            if v != ZERO else ZERO for r, v in enumerate(bins)]


def lift_aliases(bins, d):
    h = L / d
    nonzero = [(r if r <= d // 2 else r - d, v)
               for r, v in enumerate(bins) if v != ZERO]
    return [tuple(sum(cmath.exp(1j * r * j * h) * v[a] for r, v in nonzero)
                  for a in range(2)) for j in range(d)]


def grid_weighted_norm(u, h):
    return math.sqrt(h * math.fsum(abs(x) ** 2 for row in u for x in row))


def grid_a(u, h):
    d = len(u)
    return [tuple((2 * u[j][a] - u[(j + 1) % d][a] - u[(j - 1) % d][a]) / h ** 2
                  + (1 if a == 0 else -1) * u[j][a] for a in range(2)) for j in range(d)]


def grid_b(u, h):
    return [(v[1], v[0]) for v in u]


def stage_residual(u, v, alpha, h, operator):
    au, av = operator(u, h), operator(v, h)
    return [tuple(v[j][a] - u[j][a] + 1j * alpha * (av[j][a] + au[j][a])
                  for a in range(2)) for j in range(len(u))]


def check_small_grid(d, k):
    h = L / d
    initial = exact_initial_aliases(d)
    initial_grid = lift_aliases(initial, d)
    direct = [exact_initial_value(j * h) for j in range(d)]
    geometric_error = grid_weighted_norm(alias_difference(initial_grid, direct), h)
    reduced_a = [matrix_vector(matrix_add(matrix_scale(symbol(r, d), IDENTITY), Z), v)
                 for r, v in enumerate(initial)]
    intertwining = grid_weighted_norm(alias_difference(grid_a(initial_grid, h),
                                                       lift_aliases(reduced_a, d)), h)
    first = [matrix_vector(cayley(matrix_add(matrix_scale(symbol(r, d), IDENTITY), Z),
                                  k / 4), v) for r, v in enumerate(initial)]
    second = [matrix_vector(cayley(X, k / 2), v) for v in first]
    f, s = lift_aliases(first, d), lift_aliases(second, d)
    residual_1 = grid_weighted_norm(stage_residual(initial_grid, f, k / 4, h, grid_a), h)
    residual_2 = grid_weighted_norm(stage_residual(f, s, k / 2, h, grid_b), h)
    next_aliases = evolve_grid_aliases(initial, d, k, 1)
    next_grid = lift_aliases(next_aliases, d)
    norm_discrepancy = abs(alias_weighted_norm(next_aliases) - grid_weighted_norm(next_grid, h))
    unitary_discrepancy = abs(grid_weighted_norm(next_grid, h) - grid_weighted_norm(initial_grid, h))
    require(max(geometric_error, intertwining, residual_1, residual_2,
                norm_discrepancy, unitary_discrepancy) < 2e-10,
            'Small-grid geometric, wrapped-stencil, or Cayley check failed')
    return {'d': d, 'h': h, 'k': k, 'geometric_initial_sample_discrepancy': geometric_error,
            'wrapped_stencil_intertwining_discrepancy': intertwining,
            'first_stage_residual': residual_1, 'second_stage_residual': residual_2,
            'finite_alias_norm_discrepancy': norm_discrepancy,
            'unitary_step_norm_discrepancy': unitary_discrepancy}


def aliasing_control():
    # Frequencies d, 2d, ..., Kd all sample as the constant mode. Their
    # coefficient l2 norm is 1/sqrt(K), while their sampled norm stays sqrt(L).
    rows = []
    d, cutoff = 8, 1
    for count in (4, 16, 64):
        bins = [ZERO for _ in range(d)]
        v = vector_scale(1 / count, V_PLUS)
        for j in range(1, count + 1):
            bins[(j * d) % d] = vector_add(bins[(j * d) % d], v)
        measured = alias_weighted_norm(bins)
        invalid_bound = math.sqrt(L / count)
        require(measured > 1.9 * invalid_bound and abs(measured - math.sqrt(L)) < 1e-13,
                'Coherent aliasing control failed')
        rows.append({'grid_size': d, 'cutoff': cutoff, 'tail_mode_count': count,
                     'frequencies': [j * d for j in range(1, count + 1)],
                     'coefficient_l1_mass': 1.0, 'coefficient_l2_norm': 1 / math.sqrt(count),
                     'sampled_weighted_norm': measured, 'invalid_l2_sample_tail_bound': invalid_bound,
                     'norm_to_invalid_bound_ratio': measured / invalid_bound,
                     'valid_l1_sample_tail_bound': math.sqrt(L)})
    return {'passed': True, 'qualification': 'Finite coherent alias blocks disprove a uniform '
            'sample-tail estimate from the coefficient l2 norm alone. Their frequencies '
            'are all above the cutoff. The l1 bound remains valid.', 'cases': rows}


def main():
    root = Path(__file__).resolve().parent
    mass = coefficient_mass()
    omitted_coefficient_tail = coefficient_tail(REFERENCE_RADIUS)
    omitted_reference_bound = math.sqrt(L) * omitted_coefficient_tail
    require(all(abs(vector_norm(v) - 1) < 1e-15 for v in (V_ZERO, V_PLUS, V_MINUS)),
            'The three seed spinors must have unit norm')
    levels = []
    small_grids = []
    for cutoff in (1, 2, 3, 4, 6, 8):
        d, n = 8 * cutoff ** 3, 6 * cutoff ** 4
        h, k, horizon = L / d, 1 / n, 1.0
        ct, cs = 1000 * (cutoff ** 2 + 2) ** 3, cutoff ** 4 / 8
        require(d > 2 * cutoff and cutoff * h <= 1 and 2 * k * (cutoff ** 2 + 2) <= 1,
                'Refinement schedule violates theorem hypotheses')
        initial = exact_initial_aliases(d)
        reference = finite_reference_aliases(d, REFERENCE_RADIUS, horizon)
        initial_cutoff = finite_reference_aliases(d, cutoff, 0)
        terminal_cutoff = finite_reference_aliases(d, cutoff, horizon)
        tail = coefficient_tail(cutoff)
        tail_bound = math.sqrt(L) * tail
        initial_tail_error = alias_weighted_norm(alias_difference(initial, initial_cutoff))
        terminal_tail_error = alias_weighted_norm(alias_difference(reference, terminal_cutoff))
        require(initial_tail_error <= tail_bound + 1e-12 and
                terminal_tail_error + omitted_reference_bound <= tail_bound + 1e-12,
                'An endpoint truncation discrepancy exceeds the analytic l1 tail bound')
        scheme_initial_cutoff = evolve_grid_aliases(initial_cutoff, d, k, n)
        cutoff_error = alias_weighted_norm(alias_difference(scheme_initial_cutoff, terminal_cutoff))
        consistency_budget = math.sqrt(L) * horizon * (ct * k * k + cs * h * h) * mass
        require(cutoff_error <= consistency_budget + 2e-10, 'Finite-cutoff comparison failed')
        cases = []
        for perturbed in (False, True):
            working_initial = list(initial)
            amplitude = 1 / (100 * cutoff ** 2) if perturbed else 0.0
            extra_mode = d // 2
            working_initial[extra_mode] = vector_add(working_initial[extra_mode],
                                                    vector_scale(amplitude, (3j / 5, 4 / 5)))
            initial_error = alias_weighted_norm(alias_difference(working_initial, initial))
            expected_initial_error = math.sqrt(L) * amplitude
            require(abs(initial_error - expected_initial_error) < 1e-12,
                    'Perturbation initial error formula failed')
            numerical = evolve_grid_aliases(working_initial, d, k, n)
            observed_error = alias_weighted_norm(alias_difference(numerical, reference))
            upper_error = observed_error + omitted_reference_bound
            bound = initial_error + consistency_budget + 2 * tail_bound
            unitary_discrepancy = abs(alias_weighted_norm(numerical) - alias_weighted_norm(working_initial))
            require(upper_error <= bound + 2e-10, 'Infinite-data error exceeds the proposed bound')
            require(unitary_discrepancy < 2e-9, 'Long-time reduced power lost excessive norm')
            cases.append({'initialization': 'perturbed_full_sample' if perturbed else 'exact_full_sample',
                          'perturbation_alias_residue': extra_mode if perturbed else None,
                          'perturbation_amplitude': amplitude, 'initial_weighted_error': initial_error,
                          'analytic_initial_weighted_error': expected_initial_error,
                          'computed_final_error_to_radius_reference': observed_error,
                          'ideal_arithmetic_full_reference_error_interval':
                              [max(0.0, observed_error - omitted_reference_bound), upper_error],
                          'proposed_error_bound': bound, 'computed_error_to_bound_ratio': upper_error / bound,
                          'unitary_power_norm_discrepancy': unitary_discrepancy})
        levels.append({'M': cutoff, 'd': d, 'h': h, 'N': n, 'k': k, 'T': horizon,
                       'Ct': ct, 'Cs': cs, 'coefficient_tail': tail,
                       'one_endpoint_sample_tail_bound': tail_bound,
                       'initial_sample_truncation_error': initial_tail_error,
                       'terminal_radius_reference_truncation_error': terminal_tail_error,
                       'terminal_truncation_upper_with_reference_tail': terminal_tail_error + omitted_reference_bound,
                       'finite_cutoff_scheme_error': cutoff_error,
                       'temporal_consistency_budget': math.sqrt(L) * ct * k * k * mass,
                       'spatial_consistency_budget': math.sqrt(L) * cs * h * h * mass,
                       'total_consistency_budget': consistency_budget,
                       'both_endpoint_tail_budget': 2 * tail_bound, 'initialization_cases': cases})
        if cutoff in (1, 2):
            small_grids.append(check_small_grid(d, k))
    for previous, current in zip(levels, levels[1:]):
        require(current['coefficient_tail'] < previous['coefficient_tail'] and
                current['total_consistency_budget'] < previous['total_consistency_budget'],
                'The scheduled tail and consistency budget must decrease')
        for p, q in zip(previous['initialization_cases'], current['initialization_cases']):
            require(q['computed_final_error_to_radius_reference'] < p['computed_final_error_to_radius_reference'],
                    'Observed full-data error did not decrease')
            q['observed_order_in_cutoff_M'] = math.log(p['computed_final_error_to_radius_reference'] /
                                                      q['computed_final_error_to_radius_reference']) / math.log(current['M'] / previous['M'])
    alias_control = aliasing_control()
    data = {'schema': 'ndea.exp009.absolute-summable-fourier-diagnostics.v1', 'passed': True,
            'scope': 'Floating-point diagnostics only. Infinite geometric signed Fourier data '
                     'for the constant noncommuting spinor split. The explicit omitted-tail bound '
                     'controls mathematical reference truncation in exact arithmetic, not numerical roundoff.',
            'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'datum': {'q': Q, 'a_0': 'v_zero', 'a_m_for_positive_m': '(i*q)^m * v_plus',
                      'a_minus_m_for_positive_m': '(-i*q)^m * v_minus',
                      'seed_spinors': {name: [[z.real, z.imag] for z in v]
                                       for name, v in [('v_zero', V_ZERO), ('v_plus', V_PLUS), ('v_minus', V_MINUS)]},
                      'coefficient_l1_mass': mass, 'tail_formula': '2*q^(M+1)/(1-q)',
                      'initial_sampling': 'Full infinite series through closed geometric alias sums; no initial spectral truncation.'},
            'reference': {'radius': REFERENCE_RADIUS, 'mode_count': 2 * REFERENCE_RADIUS + 1,
                          'omitted_coefficient_l1_tail': omitted_coefficient_tail,
                          'omitted_weighted_sample_tail_bound': omitted_reference_bound,
                          'qualification': 'The exact analytic formula bounds the omitted series tail at every time. '
                                           'Its displayed float and the computed-error intervals are not interval-arithmetic certificates.'},
            'schedule': {'d': '8*M^3', 'N': '6*M^4', 'k': '1/(6*M^4)', 'T': 1,
                         'cutoffs': [row['M'] for row in levels]},
            'refinement': levels, 'small_grid_checks': small_grids,
            'aliasing_l2_sensitivity': alias_control,
            'summary': {'refinement_levels': len(levels), 'global_cases': sum(len(r['initialization_cases']) for r in levels),
                        'endpoint_tail_checks': 2 * len(levels), 'small_grid_cases': len(small_grids),
                        'aliasing_cases': len(alias_control['cases']),
                        'maximum_final_error_to_bound_ratio': max(c['computed_error_to_bound_ratio'] for r in levels for c in r['initialization_cases']),
                        'finest_exact_initial_error': levels[-1]['initialization_cases'][0]['computed_final_error_to_radius_reference'],
                        'finest_perturbed_initial_error': levels[-1]['initialization_cases'][1]['computed_final_error_to_radius_reference'],
                        'finest_exact_order_in_cutoff_M': levels[-1]['initialization_cases'][0]['observed_order_in_cutoff_M'],
                        'finest_perturbed_order_in_cutoff_M': levels[-1]['initialization_cases'][1]['observed_order_in_cutoff_M']}}
    (root / 'evidence').mkdir(exist_ok=True)
    (root / 'evidence/numerical_checks.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'passed': True, **data['summary'], 'omitted_reference_tail_bound': omitted_reference_bound}, indent=2))


if __name__ == '__main__':
    main()
