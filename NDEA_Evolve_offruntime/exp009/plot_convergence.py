"""Plot accepted infinite-reference refinement data without recomputing it."""
import argparse
import datetime
import hashlib
import json
import math
from pathlib import Path
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    outputs = [args.output / ('exp009_convergence.' + suffix) for suffix in ['png', 'pdf']]
    receipt = args.output / 'exp009_convergence_receipt.json'
    if any(path.exists() for path in outputs + [receipt]):
        raise RuntimeError('Preserve existing plot outputs and receipt')
    if sha(args.input) != args.sha256:
        raise RuntimeError('Accepted numerical input hash differs')
    data = json.loads(args.input.read_text())
    if data.get('passed') is not True:
        raise RuntimeError('Numerical diagnostics have not passed')
    rows = data['refinement']
    cutoff = [row['M'] for row in rows]
    if cutoff != data['schedule']['cutoffs'] or cutoff != sorted(set(cutoff)):
        raise RuntimeError('Unexpected cutoff order')
    cases = [{x['initialization']: x for x in row['initialization_cases']} for row in rows]
    if any(set(case) != {'exact_full_sample', 'perturbed_full_sample'} for case in cases):
        raise RuntimeError('Unexpected initialization cases')
    exact = [case['exact_full_sample']['computed_final_error_to_radius_reference'] for case in cases]
    perturbed = [case['perturbed_full_sample']['computed_final_error_to_radius_reference'] for case in cases]
    bound = [max(x['proposed_error_bound'] for x in case.values()) for case in cases]
    if not all(math.isfinite(x) and x > 0 for x in cutoff + exact + perturbed + bound):
        raise RuntimeError('Logarithmic plot requires finite positive data')
    if any(max(case[k]['ideal_arithmetic_full_reference_error_interval']) > limit
           for case, limit in zip(cases, bound) for k in case):
        raise RuntimeError('Recorded diagnostic exceeds the displayed bound')

    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import ScalarFormatter

    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 11,
                         'axes.labelsize': 12, 'savefig.facecolor': 'white'})
    fig, ax = plt.subplots(figsize=(10.8, 7.2))
    fig.subplots_adjust(left=.11, right=.965, bottom=.235, top=.83)
    ax.loglog(cutoff, bound, '--', color='#77539A', lw=2.1,
              label='Conservative bound for both cases')
    ax.loglog(cutoff, exact, '-o', color='#176B87', lw=2.2, ms=6,
              label='Error · exact sampled initialization')
    ax.loglog(cutoff, perturbed, '-s', color='#C56532', lw=2.0, ms=5.5,
              label='Error · perturbed initialization')
    ax.set_xlim(.9, 9)
    ax.set_ylim(min(exact + perturbed) / 2, max(bound) * 3)
    ax.set_xticks(cutoff)
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.minorticks_off()
    ax.set_xlabel('Fourier cutoff M')
    ax.set_ylabel('Weighted grid error at T = 1')
    ax.grid(which='major', color='#C9D1D9', alpha=.55, lw=.7)
    ax.spines[['top', 'right']].set_visible(False)
    ax.legend(loc='upper right', frameon=False, fontsize=10, labelspacing=.7)
    fig.text(.11, .935, 'Experiment 009 · Infinite Fourier refinement',
             fontsize=19, weight='bold', ha='left')
    fig.text(.11, .888, 'Growing cutoff with d = 8M³, k = 1/(6M⁴), and N = 6M⁴',
             fontsize=11.5, color='#465564', ha='left')
    omitted = data['reference']['omitted_weighted_sample_tail_bound']
    radius = data['reference']['radius']
    fig.text(.11, .143,
             'Floating-point diagnostic for signed geometric Fourier data; initialization uses the full series.',
             fontsize=9, color='#465564')
    fig.text(.11, .106,
             f'Terminal reference: |m| ≤ {radius}. Analytic omitted-tail bound: {omitted:.3g}; roundoff is not enclosed.',
             fontsize=9, color='#465564')
    fig.text(.11, .069,
             'The dashed curve is the larger of the two theorem bounds. Other summable spectra may have slower tails.',
             fontsize=9, color='#465564')
    args.output.mkdir(parents=True, exist_ok=True)
    for target in outputs:
        fig.savefig(target, dpi=180)
    plt.close(fig)
    if sha(args.input) != args.sha256:
        raise RuntimeError('Numerical input changed during plotting')
    record = {'passed': True, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'input_sha256': args.sha256, 'script_sha256': sha(Path(__file__)),
              'matplotlib_version': matplotlib.__version__, 'python_version': sys.version,
              'output_sha256': {p.name: sha(p) for p in outputs},
              'cutoffs': cutoff, 'initialization_cases': len(cases) * 2,
              'reference_omitted_sample_tail_bound': omitted,
              'scope': 'Plot of previously accepted floating-point data. The analytic reference tail bound does not enclose roundoff. No numerical or Lean proof rerun.'}
    receipt.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
