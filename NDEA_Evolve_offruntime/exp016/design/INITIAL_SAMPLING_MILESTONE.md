# Actual initialization sampling and interpolation

Development acceptance, September 9, 2026. Original receipts and exact source
hashes are indexed in `../evidence/INITIAL_SAMPLING_MILESTONE_LOCAL.json`.
Exp016 remains unsealed; full combined and independent qualification are pending.

Let a be the original Exp014 weighted Fourier state, c_ell its unweighted
coefficients, W0=sum_ell (1+abs(ell))^2*norm(c_ell)=norm(a), and u0=synth(a).
The grid has N=2M+1 nodes and Nh=2*pi. `sampledInitialState M h a` is exactly
the existing `Exp010.sampleSolution (2*M) h (fun _ => synth a) 0`, not truncated
data or a newly substituted sampler.

`SamplingExpansion` proves that these actual nodal samples are the summable
series of mode lifts of every original c_ell. It proves that reconstruction
minus u0 is the sum of the actual mode discrepancies. No mesh normalization
is needed for the series identities; normalization is required for the bounds.

For every natural cutoff R<=M and any spatial interval [b,b+2*pi],
`InitialSamplingBounds.sampledInitialState_spatialL2_le_tail` proves

    norm(S_h(samples(u0)) - u0)_L2
      <= 2*sqrt(2*pi)*sum_{abs(ell)>R} norm(c_ell).

All frequencies abs(ell)<=R reconstruct exactly. Every remaining discrepancy
has pointwise norm at most twice its coefficient norm. The physical L2 bound
uses the actual interval integral and its exact sqrt(2*pi) factor.

The existing weighted state hypothesis then gives, at R=M,

    norm(S_h(samples(u0)) - u0)_L2 <= 2*sqrt(2*pi)*W0/(1+M)^2.
    sqrt(h)*norm(samples(u0)) <= sqrt(2*pi)*sum_ell norm(c_ell)
                             <= sqrt(2*pi)*W0.

No extra smoothness assumption has been added. The second estimate supplies
the uniform initial physical-grid norm required by the current refinement plan.
It does not bound the evolved numerical derivatives or frequency tails.

For any numerical initial vector y0, `initialization_spatialL2_le_tail` retains
the additional term `sqrt(h)*norm(y0-samples(u0))` with coefficient one.
`InitializationCertificate` substitutes this derived initial budget into the
existing actual ordered A-half/B-full/A-half grid-time and final-partial-slab
certificates. All temporal and spatial residual contributions remain present.

`InitialSamplingLimit` proves exact-sample interpolation error tends to zero
for any M_j tending to infinity with the exact odd-grid mesh relation. Its
concrete consumer uses M_j=j+1 and h_j=2*pi/(2M_j+1). This is convergence of
initialization, not convergence of the time-stepping method.

`InitialSamplingControls` proves inclusive resolved-support exactness and the
formulas for a nonzero +1 Fourier state whose one-node samples reconstruct a
constant. The control does not assert a separately quantified positive L2 error.

All five modules passed pinned Lean 4.31.0 development checks and 22 explicit
standard-axiom reports, with no accepted warnings/errors and matching source,
log, runner, artifact and transfer hashes. Small rejected development attempts
remain preserved. The continuity repair was first checked in a separate probe;
no heartbeat/resource limits or public theorem statements were weakened.

The previous Colab VM disappeared before the first new compiler run. A fresh
normal CPU runtime restored the unchanged pins and 37 accepted artifacts;
196 project payloads, 57 bootstrap logs and 60 library roots were hash-checked.
This is imported-artifact development recovery, not independent qualification.

Next: dimension-independent sampled-potential/operator perturbation bounds,
then the actual evolved-tail/moment control or justified smooth-approximation
and uniform-stability comparison needed for solver convergence. Infinite data
tails and weighted norms remain analytical quantities until validated numeric
upper bounds are supplied; no floating-point implementation is certified here.
