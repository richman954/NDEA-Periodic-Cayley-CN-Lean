# Experiment 010 — classical infinite Fourier solution

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

The next milestone upgrades Experiment 009's infinite Fourier evolution to a
classical periodic solution of the same noncommuting spinor problem:

\[
iU_t=-U_{xx}+(Z+X)U,\qquad x\in\mathbb R/(2\pi\mathbb Z).
\]

Assume the actual coefficient sequence satisfies
\(\sum_{m\in\mathbb Z}(1+|m|)^2\|a_m\|<\infty\).
The proof must establish existence of the time derivative and both spatial
derivatives, their infinite-series formulas, joint continuity, and the
pointwise PDE. Differentiation under the sum must follow from this moment
condition, without taking derivative exchange as a hypothesis.

The resulting classical solution will be connected to actual samples in the
Experiment 009 grid error estimate. Its growing-cutoff schedule will converge
to those samples at the common terminal time one. An infinite-support regular
coefficient witness and exact controls will establish that the hypotheses and
endpoints apply beyond finite Fourier sums.

Acceptance requires all new modules and a combined source to pass Lean, audits
of every new public theorem/control, an independent combined proof check on a
fresh Colab CPU VM, validated downloaded evidence, and a sealed review packet.
Downloaded pinned compiler and compatible library artifacts remain trusted
inputs; project proof artifacts are excluded from final combined import paths.
Floating-point derivative diagnostics are supplementary evidence.

Experiment 009 and all earlier sealed files are preserved. Variable spatial
potentials, uniqueness, interpolation convergence, weaker coefficient spaces,
and a universal second-order mesh rate for arbitrary infinite data are outside
this milestone.
