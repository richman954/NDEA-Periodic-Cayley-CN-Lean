# Density and potential perturbation: a later convergence option

Status: read-only mathematical design review, September 9, 2026 UTC. No new Lean theorem, compiler check, completed convergence result, or Exp017 selection is claimed. This note checks a possible route after convergence has been proved on an explicit smooth core. It does not change the Exp016 endpoint.

The concrete planned grid consumer has fiber ℂ²; references below to the full Exp014 class mean its second-weighted Fourier data/potentials in that fixed fiber. A broader Hilbert-fiber implementation needs the corresponding discrete operator/resolvent interface.

The proposed perturbation bounds are correct in the **induced Hilbert-space operator norm**, with the assumptions below. They offer a way to avoid requiring mesh-uniform high graph norms for every datum and potential in the full Exp014 class. They do not remove the consistency/convergence proof for the smooth core.

## Cayley resolvent identity and its constant

Let G and K be Hermitian operators on the same finite-dimensional complex Hilbert space, and let a be real. Write D_G=I+i a G, R_G=D_G⁻¹ and C_G=(I−i a G)R_G, using the actual numerator-times-inverse order. The saved finite-matrix API proves invertibility of D_G and unitarity of C_G for every real a. Then

```text
C_G = I − 2 i a G R_G = 2 R_G − I,
R_G − R_K = R_G (D_K − D_G) R_K
            = i a R_G (K − G) R_K,
C_G − C_K = 2 i a R_G (K − G) R_K.
```

These identities do not assume G and K commute. Hermitian resolvents satisfy ||R_G||≤1: directly, ||D_G z||²=||z||²+a²||Gz||²≥||z||². A low-cost alternative using the accepted unitarity theorem is R_G=(C_G+I)/2, followed by the operator-norm triangle inequality. Consequently

```text
||C_G(a) − C_K(a)|| ≤ 2 |a| ||G−K||.
```

There is no dimension, mesh, ||G|| or ||K|| factor in this bound, and a=0 is valid. For the Lean matrix interface the intended norm is `‖SpinorGrid.op (G-K)‖`, or the equal difference of those continuous linear maps. A default `Matrix` norm must not silently replace this induced Euclidean operator norm. Extension to arbitrary unbounded operators would require domain/resolvent results not used here.

Relevant existing API: `exp007/lean/SpinorGrid.lean`, definitions `den`, `num`, `resolvent`, `cayleyMatrix`, and theorems `den_isUnit`, `den_mul_resolvent`, `resolvent_mul_den`, `step_mem_unitary`. Exp016's accepted `SplitDefect` uses the same actual Cayley factors. The perturbation theorem itself has not been formalized in this review.

## Actual symmetric step and many steps

On one fixed grid use the same Hermitian A and real k in both methods, and change only the middle Hermitian B to B̃:

```text
S_B = C_A(k/4) C_B(k/2) C_A(k/4).
```

The two common outer factors are unitary. Therefore

```text
||S_B − S_B̃|| ≤ |k| ||B−B̃||,
||S_B^N − S_B̃^N|| ≤ N |k| ||B−B̃||.
```

The second inequality follows from the noncommutative telescoping identity
S^N−T^N=Σ(j=0,…,N−1) S^(N−1−j)(S−T)T^j and the contraction bounds for every factor. No A/B commutation is used. For k≥0 and Nk≤T, the operator bound is at most T||B−B̃||. The application to states must retain their size:

```text
||S_B^N y₀ − S_B̃^N z₀||
  ≤ ||y₀−z₀|| + T ||B−B̃|| ||z₀||.
```

It is not a state-error bound by T||B−B̃|| alone unless ||z₀||≤1 is supplied. With physical grid norm ||y||_h=√h||y|| and h>0, exactly the same operator constant holds and the initial norms become physical norms. Variable positive steps with a common grid/order have the analogous sum Σ k_j||B_j−B̃_j||; the fixed-step statement is enough for the proposed first refinement family. Inexact solves require their own additional accumulated errors.

For the planned split A_h=L_h⊗I+I⊗Z and B_h(V)=diag_j(V(x_j)−Z), A_h remains fixed under potential approximation. A concrete block-diagonal norm lemma gives

```text
||B_h(V)−B_h(W)|| ≤ max_j ||V(x_j)−W(x_j)|| ≤ δ_V,
```

provided ||V(x)−W(x)||≤δ_V pointwise on the period. Each sampled block must be Hermitian. This is a bound on the actual block-diagonal sampled matrix, not a claim about the norm of aliased Fourier coefficients. For continuous potentials on the compact period the required uniform bound is natural. Arbitrary measurable L∞ representatives do not automatically support point sampling. The concrete sampled-matrix adapter and its norm/Hermiticity lemmas remain proof obligations.

If the full DFT reconstruction J_h has the proved physical isometry ||J_h y||L2=||y||_h, these state perturbation estimates transfer exactly to reconstructed spatial fields at numerical time nodes. No dimension-dependent pointwise inverse estimate is needed. This observation does not, by itself, control the separate quadratic time interpolant between nodes: its correction contains additional H_h and velocity terms.

## Continuum potential perturbation from the Exp015 interface

Let u solve i u_t=−u_xx+V u with initial datum f, and let v solve i v_t=−v_xx+W v with initial datum g. Assume both are classical periodic solutions in the accepted sense, period L>0, both potentials are continuous and pointwise selfadjoint, and ||V(x)−W(x)||≤δ_V. Viewed against V, the **actual** residual of v is

```text
R_V[v] = (W−V)v.
```

Thus Exp015 residual/forcing stability, the multiplication estimate
||(W−V)v||L2≤δ_V||v||L2, and conservation of v's L2 norm imply for 0≤t≤T:

```text
||u(t)−v(t)||L2 ≤ ||f−g||L2 + t δ_V ||g||L2.
```

The sign of the residual is W−V; the norm estimate is symmetric in that difference. `ResidualField.classical_regular`, `ResidualEstimate.residual_error_continuous_potential`, and `ForcedStability.classical_same_forcing_l2_eq` provide the relevant accepted interfaces. Exp014's `solution_classical` supplies the actual solutions for its regular Fourier potentials/data. A named two-potential theorem and the pointwise-operator-to-L2 multiplication bound are still small corollaries to formalize; no existing theorem is being misreported as already spelling out this full estimate.

## Dense core and the order of limits

For the Exp014 class, choose symmetric Fourier cutoffs V_r of V and finite Fourier cutoffs f_r of f. Its second-weighted absolute summability implies unweighted absolute summability. Hence the character norm-one bounds give uniform tails

```text
δ_f,r = sup_x ||f(x)−f_r(x)|| → 0,
δ_V,r = sup_x ||V(x)−V_r(x)|| → 0.
```

Symmetric cutoff preserves `v(-m)=star(v(m))`, so V_r is pointwise Hermitian. Finite Fourier data/potentials have every coefficient moment finite, but a proof of higher regularity of their **evolved solutions** is still required for whichever smooth-core consistency argument is selected. A variable-potential solution does not stay Fourier-band-limited merely because its initial datum and potential are trigonometric polynomials.

Literal sampling is not uniformly bounded from arbitrary L2 data to a grid. Here uniform Fourier approximation resolves that issue explicitly. With N h=L,

```text
||P_h(f−f_r)||_h ≤ √L δ_f,r,
||P_h f_r||_h ≤ √L ||f_r||∞.
```

The partial sums have a uniform sup bound by Σ_m||f̂_m||, independent of r. For a fixed cutoff and sufficiently fine full DFT grid, the stronger identities J_h P_h f_r=f_r and ||P_h f_r||_h=||f_r||L2 hold. They also prove interpolation consistency for the original datum:

```text
||J_h P_h f−f||L2 ≤ 2 √L δ_f,r
```

once the grid resolves f_r; then take the cutoff to infinity. These assertions require the actual DFT inversion/isometry and exact reconstruction of resolved trigonometric polynomials, not merely the older discrete Parseval formula.

Suppose convergence on the smooth core has separately been proved along one chosen refinement family, uniformly at numerical nodes t_n≤T for every fixed r:

```text
E_core(h,k,r) = sup_(t_n≤T)
  ||J_h S_(V_r)^n P_h f_r − u_(V_r,f_r)(t_n)||L2 → 0.
```

Apply the triangle inequality between the actual V/f method, the V_r/f_r method and the two continuum solutions. The bounds above give

```text
sup_(t_n≤T) ||J_h S_V^n P_h f − u_(V,f)(t_n)||L2
  ≤ E_core(h,k,r) + 2 √L δ_f,r
      + T δ_V,r (√L||f_r||∞ + ||f_r||L2).
```

The last two terms tend to zero as r grows and their constants are independent of h,k,N. Fix r first, take the mesh/time limit to eliminate E_core, then take r→∞. Constants in the smooth-core proof may depend strongly on r; they need not be uniform over all approximants. This is the precise sense in which density can avoid proving high graph-norm bounds for every original Exp014 datum/potential. A diagonal choice r=r(h) is unnecessary for qualitative convergence and needs additional estimates if used to obtain a rate.

For arbitrary numerical initial states with ||J_h y₀,h−f||L2=η_h→0, the same argument can retain η_h explicitly. Once the grid exactly resolves f_r, its right-hand side can be bounded by E_core+η_h+2||f−f_r||L2+2Tδ_V,r||f_r||L2. This preserves the full initialization mismatch. For the actual sampled initialization, the uniform-tail interpolation argument above supplies η_h→0 rather than assuming it away.

## What remains open

- Prove the dimension-free Cayley perturbation theorem, actual sampled-block norm/Hermiticity bounds and the continuum two-potential corollary in Lean.
- Complete the faithful full-grid DFT reconstruction/norm interface and initialization consistency.
- Prove convergence for each fixed smooth core pair for the **actual** ordered Cayley trajectory and an explicit refinement family. Exp016's exact residual certificate alone does not establish that its spatial residual vanishes. Uniform control of required derivatives/graph quantities on that fixed core, or another rigorous consistency argument, is still necessary.
- Match the mode of convergence: a nodewise-uniform core result yields nodewise-uniform convergence by this argument; a weaker core result cannot silently yield more. Convergence of the quadratic time reconstruction, quantitative rates, arbitrary rough L2/L∞ data under point sampling, unbounded-operator extensions and general inexact/time-dependent variants need further work.

The perturbation bound is independent of Laplacian stiffness even if ||A_h|| grows like h⁻². This does not make spatial consistency automatic, furnish uniform high graph norms, or imply operator-norm convergence over the entire L2 unit ball. It supplies a stable approximation bridge once a dense-core convergence theorem actually exists. The option is mathematically sound and worth retaining for later selection; it is not a replacement for unfinished Exp016 obligations.

An independent algebra cross-review by the QuadraticTime module owner confirmed the resolvent sign, constants, induced-norm requirement, retained initial-state factor and absence of a commutativity requirement. Both reviews were read-only and performed no compiler checks.
