# Concrete periodic split residual derivation

We take a circle of length L=2π and the smooth mode U(t,x)=exp(i(x−2t)).
It satisfies i U_t=−2 U_xx. The two split operators are A=B=−∂xx.
Both send U to U. This is a nonconstant, nonzero, commuting example.

The physical grid has d points, h>0 and d h=L. Its forward permutation P
uses the cyclic last-to-first entry. The matrix H_h=h⁻²(2I−P−P*) is
Hermitian. Periodicity and d h=L identify its corner samples with the
unwrapped x±h samples; no boundary equality is assumed separately.

The exact stencil symbol on exp(ix) is

    λ_h=(2−2 cos h)/h².

For 0<h≤1, the library cosine bound
|cos h−(1−h²/2)|≤5h⁴/96 implies |λ_h−1|≤5h²/48≤h²/8.
This establishes the spatial error instead of inserting a consistency premise.

Write φ(x)=exp(ix). For one Cayley factor with parameter α and exact source
φ(x), exact target φ(x−2α), its unscaled measured residual is

    r=(1+iαλ_h)φ(x−2α)−(1−iαλ_h)φ(x)
     =φ(x−α)·2i·(αλ_h cos α−sin α).

For 0≤α≤1, |cos α−1|≤α²/2 and the library sine Taylor bound imply
|sin α−α|≤α³/4. Consequently |α cos α−sin α|≤α³, and

    |r|≤2α³+αh²/4.

The exact split reference phases are s, s+k/2, s+3k/2, s+2k. They have
Cayley parameters k/4, k/2, k/4. For 0≤k≤2 all three estimates apply.
The h-weighted Euclidean norm of a vector bounded pointwise by R is at most
sqrt(d h)R=sqrt(L)R. Summing all three actual factor residuals gives

    stageResidualBudget ≤ sqrt(L)·[(5/16)k³+(1/4)kh²]
                        = k·(Ct k²+Cs h²),
    Ct=(5/16)sqrt(2π), Cs=(1/4)sqrt(2π).

The reference at stage j is U(jk,x). Exp005's actual fixed-time theorem then
gives weighted_error_N≤weighted_error_0+T(Ct k²+Cs h²), for Nk≤T.
The constants are independent of d, h, and the growing norm of H_h.
The varying-mesh corollary takes h_q→0, k_q→0 and initial weighted error→0,
with N_q k_q≤T, and proves the scalar final weighted error tends to zero.

Scope: one first Fourier mode, fixed period 2π, commuting equal Laplacian
splits, centered periodic discretization, bounded h and k. This does not
establish consistency for a noncommuting split, variable potential, arbitrary
smooth data, or an interpolated continuum norm. The restrictions h≤1 and
k≤2 are explicit analytic Taylor restrictions. Constants are sufficient and
not claimed sharp.

The grid is nonempty under its physical assumptions. A concrete admissible
choice is d=8, h=π/4, k=1. The spatial term is necessary: for a fixed
admissible grid λ_h≠1, the budget is of order k as k→0, not just k³.

Proof status is recorded separately. A drafted Lean file is not evidence of
compilation. Numerical diagnostics are supporting checks, not proofs.
