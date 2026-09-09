# Experiment 013 — source, scope and evidence review

The frozen source and modular-evidence review passed with no remaining blocking
finding. This is a dated source review, not the final combined-proof receipt.
The local and fresh-VM combined checks and receiving qualification were still
pending when this review was prepared. Final completion requires their actual
accepted receipts and the separate gates in `finalize.py`.

Combined source SHA-256:
`b14e205da846e45c0ac506e9319a0f351e5148232ee4fc608193709734cd4788`.

## Exact reviewed catalog

The public catalog was enumerated separately from the generator and compared
name-for-name with the 64 audit commands in the reconstructed source. Its 46
production results include supporting lemmas as well as the main endpoints;
the remaining 18 declarations are exact controls.

| Module | Public declarations | Accepted modular check |
| --- | ---: | ---: |
| GenericClassical | 18 | Exit 0; 169.483 seconds |
| GenericEnergy | 13 | Exit 0; 204.159 seconds |
| GenericUniqueness | 8 | Exit 0; 175.123 seconds |
| LegacyBridge | 7 | Exit 0; 156.924 seconds |
| Controls | 18 | Exit 0; 227.469 seconds |

All five accepted receipts match the frozen source bytes. Their log hashes
and compiled output hashes were checked again. GenericEnergy and
GenericUniqueness retain nonblocking unused-section-variable warnings; these
do not change their hypotheses or checked conclusions. Failed development
attempts are preserved and are not the accepted modular checks.

## Preserved first attempt and corrected source

The first combined source failed locally (605.823 seconds) and on its initial
Colab VM (397.123 seconds). Both logs show the same ambiguity: inherited
`Matrix` opening supplied a second interpretation of the control's unqualified
`smul_apply`. Its intended simplification then failed, so those combined runs
were rejected. The original source, modular evidence, failed combined results,
deliveries, infrastructure bindings and pending review remain under
`attempts/r1/`; none is presented as accepted final combined evidence.

The corrected Controls source changes only that proof reference to
`_root_.smul_apply`. The mathematical definitions, theorem statements and
64-name public catalog are unchanged. Its repeated modular check passed with
an empty log, and the compiled output bytes agree with the earlier successful
standalone module. The other four accepted modular sources are unchanged.
Both complete combined checks are repeated for the corrected source.

The corrected independent session is `exp013-independent-check-r2`, VM
`m-s-kkb-use1c2-3vyfjmsvu7xz8`, boot
`f7323458-d65c-4ed0-9889-e70929f24694`. The updated receiver requires the first
Experiment 013 VM in its predecessor history and rejects reuse of that VM or
its boot ID. All 16 updated offline protocol tests passed, including the
reused-VM control targeting the first Experiment 013 allocation. Input and
source-review acceptance remain separate from the pending combined results.

## Mathematical review

The generic predicate explicitly requires actual time and first/second space
derivatives, their specified joint continuity, spatial periodicity, and the
pointwise forced Schrödinger equation. It contains no assumed energy law or
Fourier representation. The potential is a bounded complex-linear operator
at each point; no uniform operator-norm bound is assumed. Its pointwise
self-adjointness is a separate hypothesis of the balance and uniqueness
results. No finite-dimensional fiber assumption is used.

With the inner product linear in its second argument, the PDE gives
`u_t = i u_xx - i V u - i f`. The real part of the potential contribution
vanishes by self-adjointness. The extra term in the spatial flux derivative
vanishes because the inner product of a vector with itself is real. The
result is `rho_t = J_x + W`, with `W = 2 Re <u,-i f>`. This sign agrees with
the exact forced control. The chosen `J` is opposite to the current in the
convention `rho_t + j_x = W`.

Continuity of forcing work follows from its equality to the difference of
the continuous density and flux derivatives. No continuity of the forcing
or potential is inserted implicitly. The local compact-rectangle bound
justifies differentiation under the scalar interval integral. Actual spatial
differentiation of the periodic solution proves periodicity of its derivative
and flux, so the boundary term cancels.

The interval identities hold for every real `L` as oriented integrals. Their
interpretation as mass or squared L² distance uses `L > 0`; they do not claim
conservation of Hamiltonian expectation. For solutions with a common potential
and forcing, subtraction gives the homogeneous equation, hence conserved
distance. Positive period and continuity then turn zero interval energy into
pointwise equality. Using arbitrary interval bases includes every endpoint.
The zero-period control demonstrates failure of integral separation only;
it is not presented as a PDE nonuniqueness example.

The legacy bridge is a field-by-field equivalence with the unchanged Exp010
classical predicate for `E 2`, period `2*pi`, potential `Z+X`, and zero forcing.
Its uniqueness proof invokes the generic theorem. Regular-data existence and
the numerical reconstruction/error endpoints retain the earlier exact data,
initialization, refinement schedule and closed-rectangle assumptions.

The controls establish a nonzero nonconstant stationary solution
`u=2+sin x` with a continuous, periodic, active nonconstant real potential
`V=-sin x/(2+sin x)`, then apply the generic conservation and uniqueness
theorems to it. The forced solution `u=t`, `V=0`, `f=i` checks `W=2t`, the
formula `energy=L*t^2`, and its actual derivative. A same-data example with
different forcing checks the shared-forcing requirement.

These results concern existing classical solutions. They do not construct
solutions for arbitrary variable potentials, establish rough spatial L²-data
evolution, prove forcing norm estimates, or extend numerical convergence to
variable potentials. Conserved distance between existing solutions is not
asserted to be a one-parameter unitary group. Independent peer review of the
generic local argument, legacy bridge and final controls found no blocker.

## Verification and preservation review

The component hashes, complete catalog and combined source reconstruct exactly.
The six-file bootstrap archive and fourteen-file final delivery archive were
read back against their complete manifests and current local inputs. The
bootstrap driver and launcher pins agree with the delivery receipt. The
initial VM record identifies the distinct fresh allocation. These input checks
do not establish that its later proof check has completed.

The infrastructure record preserves all 16 passing offline protocol checks
and the final frozen-input audit. Final verification excludes project build
artifacts, re-elaborates the retained predecessor bodies, and checks complete
axiom logs against the standard three-axiom allowlist. The compiler and
compatible external artifacts remain trusted inputs; they are not rebuilt
from source by this workflow.

The finalizer was reviewed against the actual Exp012 baseline keys, accepted
transfer schema and `exp013/` ZIP prefix. A missing stable-document hash gate
was found during review and repaired before final pinning. It now binds its
own reviewed bytes and all four stable reviewed documents, in addition to
source, delivery and accepted evidence bytes. Its known PLAN status update is
separate from those stable document pins. The final report also explicitly
distinguishes positive-period mass from general oriented interval identities.

See `evidence/REVIEW_CHECK.json` for exact source, catalog, modular-receipt,
log, output, tool, document, delivery and infrastructure bindings. This review
did not rerun Lean or access a remote service. Later final result, transfer
and packet receipts establish completion; they must not be inferred solely
from this source-review pass.
