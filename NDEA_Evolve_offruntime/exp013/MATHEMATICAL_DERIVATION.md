# Generic energy calculation and scope

Let H be a complex Hilbert space and let V(t,x) be a bounded selfadjoint
complex-linear operator on H at each point, with no uniform operator-norm
bound assumed. Let u and f satisfy the actual
classical equation

    i u_t = -u_xx + V(t,x)u + f(t,x),    u(t,x+L)=u(t,x).

The predicate records existence of the actual first time derivative, first
and second spatial derivatives, and joint continuity of u and those derivatives.
It contains neither an energy identity nor a Fourier representation. V and f
are allowed to vary in time and space. No continuity or periodicity of V/f is
needed for these conditional energy results. This does not establish existence
of a classical solution for arbitrary such inputs.

Mathlib's complex inner product is conjugate-linear in the first argument and
linear in the second. Define

    rho = ||u||^2,
    D = 2 Re <u,u_t>,
    J = 2 Re <u,i u_x>,
    Q = 2 Re <u,i u_xx>,
    W = 2 Re <u,-i f>.

The derivative of squared norm is D. The spatial derivative of J is Q:
the additional term 2 Re <u_x,i u_x> vanishes. Multiplication of the PDE by
-i gives u_t = i u_xx - i V u - i f. Selfadjointness implies that <u,V u>
is real, hence Re <u,-i V u>=0. Thus D=Q+W and rho_t=J_x+W.
The sign convention uses J opposite to the current in rho_t+j_x=W.

The joint continuity assumptions on u, u_t, and u_xx imply continuity of D
and Q. The exact PDE identity implies W=D-Q and therefore joint continuity
of W, even though no extra continuity hypothesis on f or V was imposed.

For any real base b, define E(t)=integral_[b,b+L] ||u(t,x)||^2 dx. A compact
local rectangle [t-1,t+1] times the closed spatial interval bounds D. This
supplies the domination needed to differentiate under the scalar interval
integral. The fundamental theorem of calculus turns integral Q into the
endpoint difference of J. Differentiating spatial periodicity proves that
u_x is periodic; J therefore has matching endpoints. Consequently

    E'(t)=integral_[b,b+L] W(t,x) dx.

With f=0, E'(t)=0 at every real time, so E is constant. For L>0, this quantity
is mass or squared L² norm; it is not Hamiltonian expectation. No positivity of L is
needed for the oriented integral identities. For the pointwise separation
and uniqueness endpoints, L>0 is required.

Two solutions u,v with the same V and f have difference w=u-v satisfying the
homogeneous equation. Therefore the integral of ||u-v||² is constant. If data
match at one time, it is zero at every time and every base b. If w(t,b) were
nonzero, continuity and L>0 would make its nonnegative norm-square integral
on [b,b+L] strictly positive. This contradiction proves equality at every real
time and position. Working with arbitrary bases also covers endpoints.

The generic modules import only Mathlib and one another. H is not required
to have finite dimension. This abstract fiber generality is distinct from
constructing evolution for rough spatial L² initial data, which is not done.

The legacy bridge proves exact equivalence with Exp010's concrete predicate
when H=EuclideanSpace C (Fin 2), L=2*pi, V=Z+X and f=0. Generic uniqueness
then identifies the previously constructed Fourier solution and its uniform
numerical reconstruction, with their original data and refinement assumptions.
No general variable-potential numerical convergence is claimed.

The main spatial control is u(t,x)=2+sin x and V(t,x)=-sin x/(2+sin x), acting
by real scalar multiplication. Its denominator is at least one. Here u_t=0,
u_xx=-sin x, and V u=-sin x, so the unforced PDE holds. The profile and
potential are both nonconstant and the potential acts nontrivially at pi/2.
The forced control u(t,x)=t, V=0, f=i gives W=2t and changing norm, checking
that forced mass conservation is not asserted. Zero-length intervals cannot
separate a nonzero constant function, checking the positivity requirement.
