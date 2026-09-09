# Experiment 013 — reusable periodic Schrödinger energy framework

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

The next extension chosen for reuse removes the fixed two-component fiber,
constant potential and fixed period from the Experiment 012 energy argument.
Work over any complex Hilbert space H, a real period L, bounded operators
V(t,x): H → H that are pointwise selfadjoint, and a forcing field f(t,x):

    i ∂t u = −∂xx u + V(t,x) u + f(t,x).

The classical predicate retains actual time/space derivatives, joint
continuity through the derivatives already required in Experiment 010,
spatial periodicity, and the actual PDE. Selfadjointness is a separate
hypothesis. Positive period is needed for integral separation and uniqueness.
No Fourier representation, energy law, or global time bound is assumed.

Derive local density/flux/forcing-work identities, then the exact derivative
of mass (the integral of squared norm). Derive continuity of forcing work
from the PDE identity, without an added regularity hypothesis on f or V.
For zero forcing, mass is conserved. For the same V and forcing, differences
solve the homogeneous equation, yielding conserved L² distance and uniqueness
from matching data at any real time. Bridge the existing concrete predicate
and numerical convergence result without changing their assumptions.

Exact controls should include a nonzero, nonconstant stationary scalar
solution with genuinely spatially varying real potential, a forcing-work
sign check, and necessary-hypothesis controls. The generic theorem includes
infinite-dimensional Hilbert fibers; it does not construct a rough-data
spatial L² evolution or prove existence for arbitrary variable potentials.
Hamiltonian expectation conservation, general forcing norm estimates,
variable-potential numerical convergence, and sharper rates are outside scope.

Modules: GenericClassical, GenericEnergy, GenericUniqueness, LegacyBridge,
Controls. Generic modules import Mathlib directly, separate from the retained
predecessor proof chain. All new public theorem/control declarations receive
an axiom audit. Acceptance requires modular and combined local Lean checks,
a distinct VM combined proof check when authorized access is available,
independent source/tool review, verified received evidence, and a sealed
review packet. Compiler and compatible external artifacts remain trusted.

Experiment 012's 171 payload hashes and sealed packet were verified before
copying its exact combined source as Exp012Foundation.lean. Preserve all
predecessor files. User backup preference: local Chromebook copies only;
do not mount Google Drive. Maintain local task state and checkpoints before
long jobs and after milestones.
