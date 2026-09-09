# Full odd-grid Fourier reconstruction: first bounded module

Status: local modular check accepted, exit 0 in 267.085 seconds. All seven public theorem audits use only subsets of `propext`, `Classical.choice` and `Quot.sound`. The module is `lean/FourierReconstruction.lean`; it imports accepted `Orthogonality` and `Reconstruction` through the pinned earlier modular chain. No sealed predecessor is modified. Exp016 remains unsealed and has no combined or independent qualification yet.

Accepted source SHA-256: `d371e36b98114f56cef229021e2f0d0aa0f12c42f77e5d7faf28bdcc2a8f3000`. The exact compiler receipt is `evidence/20260909T044647.851979Z_FourierReconstruction.json`; its complete log is adjacent. `design/FourierReconstruction_MODULE_CHECK.json` records the independent local source/log/runner/artifact hash readback and all seven audit names. One harmless unused `mul_assoc` simplification argument remains in the accepted source to preserve its checked bytes. The failed first attempt is preserved under `design/FourierReconstruction_attempts/r0`.

For M natural, N=2M+1 and `Grid (2*M)=Fin N × Fin 2`. A frequency index `m : Fin N` denotes the signed integer `oddFrequency M m = m.val-M`. Define the coefficient of arbitrary grid data y by

```text
a_m(y) = (1/N) sum_j exp(-i*(m-M)*j*h) nodeValue(y,j).
S(a)(x) = sum_m exp(i*(m-M)*x) a_m.
R_h(y) = S(a(y)).
```

The accepted first endpoint assumes only N*h=2*pi and proves `R_h(y)(j*h)=nodeValue(y,j)` for every grid state y and every node j. It then proves that existing `Exp010.sampleSolution` recovers y exactly and that reconstruction is injective. Spatial periodicity follows from integer characters. M=0 (one node) is included. No band-representation premise is imposed on y.

The proof route is an exact row character sum. Off the diagonal j=l, the frequency-index sum is a fixed centered phase times the existing `Exp008.FourierGrid.phase_sum_zero` at frequency j-l. Distinct indices in `Fin N` have nonzero difference of magnitude less than N, hence that difference is not divisible by N. On the diagonal the sum is N. Exchange the two finite sums in reconstruction and use this Kronecker-delta identity. This route avoids a separate dimension/surjectivity argument while proving fidelity to all grid states.

The first module does not claim continuum L2 Parseval, actual spatial derivatives, polynomial-time regularity, spatial consistency, small PDE residuals, or convergence. Subsequent consumers must prove those properties from these actual definitions. Its formula and norm normalization remain compatible with the full Exp016 plan; the continuum L2 identity is a separate obligation, not a consequence of sampling fidelity alone.
