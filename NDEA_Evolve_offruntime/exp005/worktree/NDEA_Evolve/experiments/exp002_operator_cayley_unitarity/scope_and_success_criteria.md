# Scope and success criteria

## Formal scope

- Finite-dimensional square matrices over `ℂ`.
- Real Cayley parameters.
- Hermitian generators for nonsingularity and unitarity.
- Fixed finite ordered products; generators and step sizes may vary and need not
  commute.
- The order-defect identity requires invertible denominators but not Hermiticity.
- The commutation equivalence additionally requires both scalar parameters nonzero.

“Variable step” means an exogenously fixed realized sequence. If a generator depends
on the evolving state, per-trajectory norm preservation does not by itself imply that
the nonlinear evolution preserves distances between different initial states.

## Required gates

- Julia exact Gaussian-rational derivation and machine-readable certificate.
- Independent validator that reconstructs matrix and symbolic identities.
- Exact noncommuting Pauli-matrix witness.
- Lean proof of denominator nonsingularity from Hermiticity, two-sided unitarity,
  finite-product unitarity, exact order defect, and the nonzero-step commutation
  criterion.
- Mathematically targeted negative controls for dropped Hermiticity, complex step,
  false order independence, wrong defect sign/order, omitted nonzero-step assumption,
  and false Cayley semigroup merging.
- Verbose Lake build with complete log; direct checks; declaration signatures;
  `#print axioms`; forbidden-token scan; exact commands and exit codes.
- Final layered SHA-256 manifests and independent Chromebook verification.
- Durable off-runtime checkpoints at preflight, Julia-green, Lean-green, preclosure,
  and final closure.
- Pre/post verification that Experiment 001's local archive hash and remote tracked
  subtree remain unchanged.

## Explicitly out of scope

- Unbounded or infinite-dimensional self-adjoint operators.
- Claims of mathematical novelty for the classical Cayley identities.
- Convergence order, Magnus/BCH error estimates, PDE well-posedness, or floating-point
  long-time conservation bounds.
- State-dependent nonlinear flow isometry.
- QGI, topology/geometry, inverse-integrator, or legacy-restore missions.

The experiment is not complete if Lean merely assumes denominator invertibility in
the Hermitian headline theorem; it must derive finite-dimensional nonsingularity.
