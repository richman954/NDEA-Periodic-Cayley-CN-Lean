# Experiment 012 source and verification review

No blocking mathematical issue was found within the stated classical
uniqueness scope. This review covers all five new modules, their public
theorem catalog, the exact controls, and the verification and preservation
workflow. The exact final reviewed versions are recorded separately in
[REVIEW_CHECK.json](evidence/REVIEW_CHECK.json). Compiler
acceptance is separate evidence; this source review does not itself rerun Lean.

## Original solution class and local identity

The conservation and uniqueness theorems use the unchanged
`Exp010.IsClassicalPeriodicSolution` predicate for
`iUt=-Uxx+(Z+X)U`, with period `2π`. The competing functions need not be
Fourier series. The predicate already requires actual time and first and
second space differentiability, joint continuity of the solution and these
derivatives, periodicity, and the PDE. The new theorems add no energy
identity, Fourier representation, or bound uniform over all real times.

`potential_selfadjoint` obtains Hermitian symmetry of the actual constant
matrix `Z+X`. Multiplying the PDE by `-i` gives
`Ut=i Uxx-i (Z+X)U`. The real part of the potential's contribution to the
norm-squared derivative is zero by selfadjointness.

The flux convention is
`J=2 Re ⟨u,i Ux⟩=-2 Im ⟨u,Ux⟩`. Differentiating it in space produces
`2 Re ⟨Ux,i Ux⟩+2 Re ⟨u,i Uxx⟩`; the first term vanishes and the second
is the actual time derivative of `‖u‖²`. Thus the proved sign is
`∂tρ=∂xJ`. In the alternative convention `∂tρ+∂xj=0`, the current is
`j=-J`. The frequency-one control fixes this sign concretely with `J=-2`.

The derivative of a periodic differentiable function is proved periodic
by differentiating its translated equality. Consequently the actual flux
is periodic. Closure under subtraction checks all fields of the original
predicate, including actual second-space differentiability and joint
continuity of all derivatives. It does not rely on the default value of
`deriv` at a nondifferentiable function.

## Integral conservation and separation

The parameter-integral theorem derives a local dominating constant from
continuity of the time-derivative integrand on the compact rectangle
`[t-1,t+1] × uIcc(a,b)`. This bounds the integrand derivative on a time
neighborhood and the spatial interval required by Mathlib's differentiation
theorem. The constant is integrable over that finite interval; the proof
also supplies slice measurability, integrability, and actual derivatives.
No global bound in time is introduced.

For every real interval base `b`, the energy is the integral of the actual
norm square over `[b,b+2π]`. Its derivative is the integral of the local
density derivative. The fundamental theorem of calculus replaces that
integral by the endpoint flux difference, and periodicity makes it zero.
Differentiability and zero derivative on all of `ℝ` give conservation
between any two real times, including times before the matching time.

The separation lemma is pointwise, rather than an unsupported passage from
almost-everywhere equality. If a continuous spinor field is nonzero at an
arbitrary point `b`, its nonnegative squared norm has a strictly positive
integral on `[b,b+L]` whenever `L>0`. The positive point is allowed to be
the left endpoint: continuity and positive interval length supply the
necessary positive-measure neighborhood. Zero integrals for every real
base therefore force the field to vanish at every real position.

Applied to the difference of two classical solutions, energy conservation
transports zero energy from the matching time to the requested time.
Continuity and separation then yield equality of the functions. The
orientation in `classical_unique_at_time` and the `ExistsUnique` endpoint
matches the claimed competing-function equality.

## Endpoints and controls

Uniqueness holds for any two functions in the stated global classical
periodic class that agree at one real time. The existence claim is narrower:
for coefficients satisfying `Regular a`, namely summability of
`(1+|m|)² ‖a_m‖`, Experiment 010's constructed infinite Fourier solution
exists and is now the unique classical solution with that initial profile.
Existence for arbitrary unrelated initial functions is not claimed.

The two reconstruction endpoints identify this unique solution with the
target of Experiment 011's existing numerical error bound and actual
`TendstoUniformlyOn` theorem. They retain the same full-grid Cayley iterate,
exact sampled initialization, explicit schedule, bound, and closed rectangle
`[0,1] × [0,2π]`. Uniqueness is global in real time and position; the
inherited uniform reconstruction theorem is stated on that rectangle.

The complete catalog has 46 declarations: 16 local energy results,
9 integral/conservation results, 3 separation results, 8 uniqueness and
reconstruction endpoints, and 10 exact controls. The controls exhibit a
nonzero frequency-one solution of norm one, singleton Fourier support,
energy `2π` at every real time and interval base, distinct classical
solutions with distinct data, zero-data uniqueness, recovery of initial
data from matching at time one, and the flux sign. The competing function
in the terminal-matching control is arbitrary within the original class.
No new floating-point simulation is used as evidence of uniqueness.

## Verification and preservation

The infrastructure is adapted from the sealed Experiment 011 workflow;
see [INFRASTRUCTURE_REVIEW.md](INFRASTRUCTURE_REVIEW.md). The retained
foundation is pinned exactly. The final combined source and complete public
catalog are reconstructed from the current modules. Project artifacts are
excluded from the final import paths, so retained predecessor proof bodies
are also re-elaborated.

The fresh-VM receiver binds allocation and boot identity, the exact
bootstrap deliveries, completed command logs, final proof inputs, compiler
audit logs, and matching external artifact manifests. The finalizer requires
accepted local, independent, and transfer receipts, current modular source
and output hashes, this review, and predecessor preservation. It refuses
existing sealed outputs, verifies every ZIP member by readback, and checks
the exact manifest bytes. Its archive receipt is external to the ZIP,
avoiding a self-hash cycle. ZIP entries use `exp012/`; readback checks that
same prefix.

Accepted compiler runs and final qualification are recorded separately in
[FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). The pinned
compiler and compatible compiled external libraries remain trusted inputs.
The result does not cover weaker solution classes, existence for rougher
data, spatially varying potentials, nonperiodic boundary conditions, or a
sharp numerical convergence rate.
