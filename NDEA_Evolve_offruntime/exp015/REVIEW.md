# Experiment 015 exact-source review

Source and review acceptance: passed. All seven current modules have successful
compiler receipts whose source, complete compiler log and artifact hashes match.
This review does not claim that the final local or independent combined checks
have passed; those checks and receiving validation remain separate gates.

The frozen combined source is `ef99d7098209d790f32abf89e2ec866e1b3c0cb2ce5b4262022df3cfdbf18846`.
The new public catalog has **50 declarations: 28 production and 22 controls**.
The unchanged Exp014 combined proof bodies, including the retained generic
Exp013 foundation, are embedded; only 143 old axiom-print commands are removed.
The new audit catalog covers Exp015. Preserved earlier packets carry their own
prior numerical qualification.

## Review roles and independence

The coordinating source reviewer authored ScalarSqrtEstimate and Controls and
independently reviewed the other five new mathematical modules. Those two
authored modules received a separate read-only review from the SpatialL2 author;
its exact-source receipt is `evidence/SCALAR_CONTROLS_CROSS_REVIEW.json`.
The root coordinator also read all seven mathematical modules and independently
reviewed the critical verification infrastructure. INFRASTRUCTURE_REVIEW.md is
the infrastructure implementer's account, distinct from that independent tool
review. Authorship is not represented as independent review of one's own code.
All these review bindings are captured in evidence/REVIEW_CHECK.json.

## Mathematical assessment

The public scalar comparison assumes nonnegative differentiable energy, a
continuous nonnegative forcing size and the actual derivative upper bound.
It differentiates sqrt(E+epsilon^2), with a proved positive denominator, then
removes epsilon by a positive-gap argument. It never assumes nonzero initial
or later error, and continuity of the energy derivative is not required.

SpatialL2 is the square root of the actual integral of the squared Hilbert
norm over [b,b+L]. On continuous fields and a positive period it has the intended
L2 meaning. The spatial Cauchy--Schwarz proof integrates a nonnegative quadratic
and uses its discriminant, covering zero factors. Joint continuity supplies
finite-interval integrability and time continuity. The forcing work estimate
has coefficient two, which becomes exactly one after the scalar comparison.

The PDE estimates use the unchanged Exp013 classical predicate and its actual
energy derivative. They require a common pointwise selfadjoint potential,
positive spatial period and jointly continuous forcing difference, for arbitrary
complete complex Hilbert fibers and spatial origins. Potential continuity is
not silently inferred. Same-forcing error size is conserved. General forcing
stability holds for every ordered finite interval s <= t.

The approximate-field predicate lists actual differentiability, joint
continuity of the field and required derivatives, and periodicity. Its residual
is exactly i*u_t + u_xx - V*u. The forced-solution bridge is proved by algebra
from this expression. Residual bounds retain the full initial mismatch; exact
initialization is a separate specialization. Jointly continuous operator
potentials supply residual continuity. A uniform residual budget accumulates
as (t-s)*delta. The Exp014 application uses its actual constructed solution,
original weighted Fourier assumptions and Hermitian symmetry.

The controls compute the actual residual i of w(t,x)=t with V=0. On period
one, error against zero and integrated residual size both equal one at time
one. They instantiate the main estimate and exact-initialization estimate,
and prove that any smaller universal coefficient would have to satisfy 1<=C.
The stationary field one has zero residual and nonzero preserved initial error,
and explicitly contradicts omission of the initial-error term. Zero-field
energy, a certified zero-error bound and the equal-time interval are checked.
No control replaces an actual PDE calculation by an assumed conclusion.

No mathematical blocker was found. This is continuum classical stability and
residual-to-error estimation. It supplies neither a regular numerical
reconstruction nor a discrete consistency/refinement theorem. Those remain
later work; no discrete convergence rate is asserted here.

## Exact tools, deliveries and evidence

The review binds reconstruction, modular/final checkers, source preparation,
fresh initialization/bootstrap/launch, export/receiving, predecessor preservation,
finalizer and the saved offline tests. The existing 62 offline controls passed
and their executed script hashes still match; unchanged tests were not rerun.
They use synthetic fixtures and are not mathematical proof evidence.

The prepared bootstrap archive hash is `2b241d475047b2bdf4b06094786fb837f2455dd5e92f23d24d296bcafd0cab05`;
the pinned launcher hash is `275bc4f63687287b0cc63c82429b88c2db11788974123359aef1bae33a3d96d4`. Its two literal pins match the
actual archive and bootstrap helper, and its Combined.lean input matches the
frozen combined source. Both source-only archives were read back at preparation.
No project artifact is delivered. Both combined checks must exclude project
artifacts from their import paths and compare exact source and external artifact
hashes before and after compilation. Lean 4.31.0 and compatible external library
binaries remain trusted inputs; they are not rebuilt from source.

The receiver must verify the independently produced complete logs, manifest,
source delivery, fresh VM/boot identity and bootstrap command sequence before
accepting transferred evidence. Finalization additionally requires current
modular/review bindings and unchanged sealed predecessors. This review grants
source/tool acceptance only; actual RESULT.json and transfer/packet receipts
establish later qualification and sealing.
