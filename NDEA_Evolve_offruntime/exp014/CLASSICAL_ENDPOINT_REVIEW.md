# Classical endpoint and controls source review

This is a source review of the active Experiment 014 implementation, not a
compiler result or an independent-runtime verification receipt. Sealed
Experiment 013 interfaces were read without modification.

## Mathematical scope

`global_classical_exists_unique` constructs the actual Experiment 013 classical
periodic solution predicate on all real times, with period `2*pi`, an arbitrary
complete complex Hilbert fiber, static potential `V(x)`, and zero forcing.
Initial coefficients and bounded-operator potential coefficients have finite
second weighted absolute Fourier moments. Hermitian Fourier symmetry supplies
pointwise self-adjointness for the uniqueness conclusion. Existence itself is
proved without the Hermitian hypothesis.

The endpoint establishes joint continuity of the solution and all required
actual derivatives. It does not assume the PDE, an energy identity, or a
Fourier representation for competing classical solutions. Uniqueness uses the
preserved Experiment 013 theorem in its full classical solution class.

The time derivative uses the strong-operator product rule after bounded
synthesis. This is the correct regularity level: the argument does not require
the physical weighted Fourier trajectory to be differentiable in its own
second-moment norm. The free contribution is `i*u_xx`; the potential contribution
is `-i*V(x)u`, giving the stated Schrödinger sign after multiplication by `i`.
Continuity of derivatives follows through bounded synthesis and joint
continuity of state evaluation, without a coordinatewise time-supremum
summability assumption.

The theorem does not assert existence with general time-dependent potentials,
forcing, rough initial data, nonlinear terms, or arbitrary spatial periods.
It does not by itself extend the previous numerical convergence theorem to
these variable potentials.

## Exact controls

The 22 public controls cover a signed single mode, the free-flow derivative
sign, a regular Hermitian potential supported at frequencies `1` and `-1`,
and distinct potential values `2` and `-2` at spatial points `0` and `pi`.
They also cover zero potential and an explicit regular initial coefficient
family that is nonzero at every integer frequency. Three endpoint
instantiations include nonconstant potential together with infinite-support
initial data. Thus the construction is not restricted to finitely many
initial modes or constant potentials.

The controls do not contain a separate theorem proving that new frequencies
are generated dynamically. No such additional statement is needed for their
stated nonvacuity scope.

## Implementation assessment

No mathematical blocker was found in the endpoint or controls during this
review. Referenced geometric-encode summability and scalar cancellation APIs
were checked in the pinned local Mathlib source. Scalar restrictions in the
strong product rule, nested derivative rewrites, and simplification of the
two special exponential values remain subject to actual Lean elaboration.

Reviewed initial source hashes:

- `lean/ClassicalExistence.lean`:
  `2271dddd4b7437fa83fc384a37af316a97468be948ec74dc2ad9c72338830c10`
- `lean/Controls.lean`:
  `f6ebfe301c217e7c0f4b795e08dbd2b89a57f9de12d47953efb54c96eb66eea9`
- `lean/GlobalLinearEvolution.lean`:
  `93a0f239ecb2707d4296681669fd8c5ce6b3f03bd91d6dff07a04c532b9fdac1`
- `lean/StrongOperatorDerivative.lean`:
  `418ca3c3ac6f4cfcd3b8a3e05230eea922a6c95656c04b806ff743abc2b90e36`

## Accepted endpoint modules

The final endpoint and controls were reviewed again after the elaboration
repairs. The statements, hypotheses, construction, and 22-control catalog are
unchanged. Changes make the CLM norm instance explicit, factor continuity
composition through an abstract topological helper, rewrite explicit function
equalities before applying derivative results, and use direct scalar
identities for `i*(-i)=1`. The zero-potential control similarly rewrites an
explicit equality of potential functions. One deprecated alias and one unused
simplification argument were removed.

Both modules passed Lean with exit zero and empty logs under the default
heartbeat limit. Their final source, log, and compiled artifact hashes were
checked against the timestamped receipts:

- `lean/ClassicalExistence.lean`:
  `74086199b1de9959d61a09d0ab8f4ae4299d683e135fc2e0a3a062b74c574a41`;
  `evidence/20260909T011651.939592Z_ClassicalExistence.json`, 93.673 seconds.
- `lean/Controls.lean`:
  `fff6851ac9d90257c1bb39dba6183854c87e2c2e522d7f82262da952ef48c96c`;
  `evidence/20260909T012436.328619Z_Controls.json`, 136.055 seconds.

Failed endpoint revisions, logs, and receipts are preserved under
`attempts/classical_endpoint_resume_r1/`, `attempts/classical_endpoint_resume_r2/`,
`attempts/classical_endpoint_resume_r3/`, and `attempts/controls_resume_r1/`.

These are local modular checks using already checked imported modules.
Final acceptance still requires the exact combined-source check and separate
fresh-runtime verification. This review does not substitute for those results.
