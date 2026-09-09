# Mathematical derivation and scope

Write C_A=Chat A(k/4), C_B=Chat B(k/2), and S=C_A C_B C_A.
Products are continuous-linear-map products, so the rightmost map acts first.
The mesh-weighted quantity is W_dx(x)=sqrt(dx)‖x‖ on the existing complex
Euclidean state space. For dx>0 it detects equality; at dx=0 it vanishes on
every state and must not be interpreted as a genuine physical norm.

## Stability and exact factor transfer

Hermiticity gives unitarity of each Cayley factor, hence W_dx(Sx)=W_dx(x),
without a bound on k, the dimension, or either generator norm. For each
factor, D=I+iαH, N=I-iαH, R=D⁻¹. The two inverse identities give RN=NR=C.
Consequently a measured residual r=D(target)-N(source) satisfies

`R r = target - C source`.

For source v, intermediate states z1,z2, and final target w, apply this
identity three times. Substitution, with the multiplication order preserved,
gives exactly

`w - S v = C_A(C_B(R_A r1)) + C_A(R_B r2) + R_A r3`.

There is no residual orthogonality, commutativity, or cancellation assumption.
Each R is a contraction, and each later C preserves norm. The triangle
inequality therefore gives W_dx(w-Sv)≤W_dx(r1)+W_dx(r2)+W_dx(r3).
This is a certificate for arbitrary supplied stage states: the residuals are
defined from those states, rather than introduced as unrelated assumptions.

## Accumulation and mesh-family convergence

For the numerical trajectory v_(j+1)=S v_j and a reference u_j, define
d_j=u_(j+1)-S u_j. Then
u_(j+1)-v_(j+1)=S(u_j-v_j)+d_j. Induction and stability yield

`error_N ≤ error_0 + sum_(j<N) W_dx(d_j)`.

The stage identity bounds each summand by the measured three-stage budget.
If k≥0, Ct,Cx≥0, N*k≤T, and the explicit per-step hypothesis is

`stage_budget_j ≤ k*(Ct*k² + Cx*dx²)` for j<N,

then error_N≤error_0+T*(Ct*k²+Cx*dx²). The factor k is necessary: a raw
per-step bound R accumulates to N*R, not T*R. The controls contain an exact
N=2,k=1/2 example exposing this difference.

For a sequence of meshes, n,A,B,N,k,dx may all vary. With common T,Ct,Cx,
the same measured residual premise, k→0, dx→0, and initial weighted error→0,
the displayed scalar majorant tends to zero. Nonnegativity and squeezing
prove convergence of the final weighted error to zero. The conclusion lives
in the real numbers; vectors in different dimensions are not silently placed
in a common function space.

## Dimension-free conversion from pointwise bounds

If each coordinate of r has norm≤R and n*dx=L, then

`W_dx(r)² = dx * sum_i ‖r_i‖² ≤ dx*n*R² = L*R²`.

Nonnegativity gives W_dx(r)≤sqrt(L)*R. This is a useful bridge for later
pointwise consistency estimates, not a derivation of such estimates itself.
The zero-dimensional case is included when the mesh identity forces L=0.

## What remains unproved

The uniform stage-residual estimate is a premise. This experiment does not
derive it from a general split differential equation or smooth solution.
It does not prove PDE well-posedness, convergence of spatial interpolants,
or an unbounded-operator theorem. Stability alone cannot imply consistency,
as a compiled zero-generator drift witness demonstrates.

Experiment 004's fixed-matrix estimate contains generator norms that may
depend on the mesh. No uniform bound on those norms is asserted or needed
here. The new residual route avoids using those norm-based constants; it
does not make the missing PDE consistency premise automatic.

The old single unsplit CN scheme also cannot substitute for the symmetric
scheme's consistency argument. With A=0 the schemes coincide, but with B=0
the symmetric scheme uses two half-A Cayley steps. A scalar operator witness
at A=I,k=2 distinguishes them exactly.
