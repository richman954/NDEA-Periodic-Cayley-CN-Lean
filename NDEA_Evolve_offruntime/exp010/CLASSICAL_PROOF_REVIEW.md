# Experiment 010 classical proof review

No blocking mathematical or statement-scope issue was found in the reviewed
production sources and mathematical derivation. This is a bounded source
review, not a replacement for the final combined and independent Lean checks.
The reviewer also implemented `ClassicalSolution.lean` and `Continuity.lean`;
this review is not independent authorship review of those two modules.

The reviewed regularity condition is precisely
`Summable (fun m => (1+|m|)^2 * ‖a m‖)`. It implies ordinary absolute
summability and supplies a uniform summable majorant for all three required
derivative series. The time majorant is twice the weighted coefficient norm;
the first and second spatial majorants are the weighted norm itself. The
frequency estimate `‖G_m‖≤m²+2` and the signs `-iG_m`, `im`, and `-m²`
agree with the retained Fourier mode and PDE conventions.

`ClassicalSolution.lean` applies `hasDerivAt_tsum` three times. The third
application differentiates the already identified first spatial derivative,
and uses summability of its series at a base point. This establishes actual
second differentiability without a fourth coefficient moment. The PDE then
follows from the per-mode equation using proved summability and continuous
linear map identities. It does not assume a derivative-exchange or PDE
identity as an extra premise.

`Continuity.lean` proves joint continuity of the solution and all three
derivatives on the real time-space plane using `continuous_tsum` and the same
global majorants. Its `IsClassicalPeriodicSolution` predicate explicitly
requires time differentiability, first spatial differentiability, and
differentiability of the first spatial derivative. This avoids relying solely
on continuity of Lean's totalized `deriv`. The predicate also includes
periodicity and the pointwise PDE. The retained initial-value series identity
remains applicable under the proved absolute summability.

`ClassicalClosure.lean` identifies actual pointwise samples of this same
classical solution with the predecessor's infinite grid reference. The norm
in its error definition compares the actual split Cayley iterate with samples
at time `N*k`, and its initial discrepancy uses samples at time zero. The
quantitative theorem retains every predecessor cutoff, non-aliasing, mesh,
step-size, and horizon restriction. The tail contribution is
`2*moment 2 a/(M+1)^2`; both endpoint tails remain included. The constants are
the existing cutoff-dependent `Ct(M)=1000*(M²+2)^3` and `Cs(M)=M⁴/8`.

The scheduled convergence theorem retains the proved growing-cutoff schedule
and a vanishing initial sampled error premise. Its exact-initial-value
specialization supplies a concrete way to satisfy that premise. The separate
time-one identity makes the common terminal time explicit. These results
concern weighted errors of pointwise samples, not an interpolated continuum
norm or an unconditional second-order rate for arbitrary infinite data.

The mathematical derivation accurately describes these statements. The
constant spin potentials `Z` and `X` do not commute, while their sum is the
bounded potential in the PDE. No spatially varying potential, uniqueness,
weaker coefficient-space theorem, or uniform rate independent of the cutoff
is claimed. The infinite-support formal witness and the separate numerical
diagnostic datum are correctly distinguished.

At the review checkpoint, the 11 derivative/PDE lemmas passed their modular
check with exit 0 in 137.386 seconds, and the 10 continuity/classical lemmas
passed with exit 0 in 118.701 seconds. The source hashes remained unchanged
during both runs. Final whole-source verification is recorded separately.

Reviewed source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `lean/Regularity.lean` | `e219924f02855f9d2abc2303b56e791a7f6cb7224779736200a4881719e59299` |
| `lean/ClassicalSolution.lean` | `6ec534b1c1413569f16e166fb3f3b68c15a3c83791748a68f10607d83390ed51` |
| `lean/Continuity.lean` | `7e26cbb8653f1a1d8926674a3f9e4d2ebfc60abfd49eb2a7b4fa0dc8984a63a6` |
| `lean/ClassicalClosure.lean` | `0084bc521a7fd4db76668d1bce8b5a0267b263878040f8f30fe51c4757ca0745` |
| `MATHEMATICAL_DERIVATION.md` | `915b6e37178bd66fb6e7d8520199f3c0a86675f4212ce74a5aa57a293d608dfa` |

Modular receipts:

- [Derivative/PDE check](evidence/20260908T100955.079833Z_ClassicalSolution.json)
- [Continuity/classical check](evidence/20260908T101307.819389Z_Continuity.json)
