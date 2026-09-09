# Experiment 009 scope review

The next bounded milestone is convergence to an actual infinite Fourier reference for absolutely summable spinor coefficients. The existing constant internal matrices still preserve each frequency. The new issue is the interaction between a growing retained band, sampling, and the unresolved Fourier tail.

For `a : ℤ → ℂ²`, assume `Σ ‖a_m‖ < ∞`. Define the reference as the actual sum `U(t,x)=Σ exp(imx) exp[-it(m²I+Z+X)]a_m`. Each mode preserves its coefficient norm, so this sum converges absolutely at every space and time point. Its sampled grid values are the sums of the actual mode lifts.

Let `band M=[-M,M]`, `mass(a)=Σ‖a_m‖`, and `tail(M,a)=mass(a)-Σ_{|m|≤M}‖a_m‖`. The finite band exhausts the integers, so `tail(M,a)→0`. Its grid contribution is bounded by `sqrt(2π)*tail(M,a)` under the exact mesh identity `(n+1)h=2π`. This uses the triangle inequality and the norm of each sampled mode. Infinite frequencies inevitably alias on any finite grid, so extending the finite-band discrete Parseval identity to the tail would be incorrect.

Applying Experiment 008 to the retained band gives, for arbitrary initial grid states and error measured against the full infinite reference,

`e_N ≤ e_0 + sqrt(2π) [T (Ct(M)k²+Cs(M)h²) mass(a) + 2 tail(M,a)]`.

The two tails arise separately when replacing the full reference by its truncation at initialization and at the terminal time. A theorem initialized exactly from the truncated band can use one terminal tail, but the arbitrary-initialization endpoint must retain both contributions or account explicitly for the full initial discrepancy.

The growing-cutoff convergence conditions are `M→∞`, `Ct(M)k²→0`, and `Cs(M)h²→0`, in addition to the finite-grid admissibility conditions on every mesh. The asymptotic growth is `Ct(M)=O(M⁶)` and `Cs(M)=O(M⁴)`. Thus a cutoff cannot grow arbitrarily quickly compared with spatial or temporal refinement. For example, a schedule with `h=O(M⁻³)` and `k=O(M⁻⁴)` makes both consistency terms vanish; constants must also enforce the exact grid-period identity and the small-step restrictions.

For quantitative tail control, a finite weighted absolute moment

`moment(r,a)=Σ (1+|m|)^r ‖a_m‖`, for natural `r`,

implies absolute summability and `(M+1)^r tail(M,a) ≤ moment(r,a)`. This is a strong and explicit coefficient regularity assumption; it is not being identified with an `H^r` Sobolev norm. Positive `r` supplies an algebraic tail rate. The exponent-zero case remains a valid inequality but gives no rate improvement.

The infinite reference is the absolutely convergent Fourier evolution. This milestone does not claim classical first time and second space derivatives under absolute summability alone. Such a claim needs a stronger weighted hypothesis and termwise differentiation. The local pinned Mathlib has `hasDerivAt_tsum` in `Mathlib.Analysis.Calculus.SmoothSeries`; a summable `O(m²+2)‖a_m‖` majorant is a plausible subsequent bounded extension. Spatially varying potentials and frequency mixing remain a separate problem.

Acceptance should check the actual sum definitions, their summability, coordinate sampling identity, periodicity and initial value; prove the sampled tail without alias-free assumptions; derive the full-reference error from Experiment 008; prove cutoff exhaustion and a concrete admissible schedule; and audit quantitative weighted-tail claims and exact controls. Numerical finite approximations remain supporting diagnostics and must declare how the uncomputed infinite remainder is bounded.
