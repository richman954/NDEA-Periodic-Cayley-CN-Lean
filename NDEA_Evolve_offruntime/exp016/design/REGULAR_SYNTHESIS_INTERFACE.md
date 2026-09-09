# Immediate regular-synthesis interface

Design only; no additional Lean acceptance is claimed here. The current consumer is the full-grid Fourier reconstruction applied to the quadratic Cayley slab. Avoid constructing a new Banach space of C2 functions.

For a complex normed state space E and Hilbert fiber H, take three families of continuous linear maps S, Dx, Dxx : real → (E →L[complex] H). Require operator-norm continuity of these families, actual pointwise derivative identities for S(x)z and Dx(x)z, and periodicity of S. These conditions have a direct finite Fourier consumer. No norm isometry or consistency bound is built into this regularity contract: prove those as separate concrete properties.

Given a state path q with a continuous actual derivative, the physical field w(t,x)=S(x)(q(t)) has actual derivatives S(x)q'(t), Dx(x)q(t), and Dxx(x)q(t). Derive all four joint-continuity fields required by the unchanged Exp015.IsRegularPeriodicField using continuity of continuous-linear-map application. Use the quadratic module for q and q', and its exact endpoints for numerical fidelity. An alternative time integrator can later supply its own path and derivative through this same immediate-consumer interface.

For a static continuum potential V(x) and grid generator G, define the actual discrepancy map

    C(x) = S(x) composed with G + Dxx(x) - V(x) composed with S(x).

Then prove the actual derivative identity

    pdeResidual V w(t,x) = S(x)(i*q'(t)-G*q(t)) + C(x)(q(t)).

This does not stipulate a forcing or assume it is small. For the quadratic q=m+tau*v-c*Gv, linearity gives Cq=Cm+tau*Cv-c*C(Gv). The accepted spatialL2 triangle/scaling rules and the separately proved Fourier L2 isometry will produce the exact PLAN budget. Positivity of the time slab gives the coefficient bounds. The actual ordered Cayley stage module supplies the endpoint defect; the stronger ordered eta identity and unitary bounds still need proof.

Exp015.residual_error_uniform_budget already accepts arbitrary real s≤t and keeps the initial error. Apply it with s=t_j and t=t_j+k_j to each globally defined slab extension. Matching endpoint values permit finite accumulation without asserting global C1 regularity of the assembled trajectory. Continuity of V and the synthesis maps will establish actual residual continuity.

For the concrete spatial discrepancy, split the grid generator into the saved centered stencil and the sampled block potential. Prove the corresponding two discrepancy identities before estimating them. The Fourier cutoff, aliasing, norm normalization and sampled-potential approximation must remain visible. No condition in this interface replaces the later proof that those concrete quantities vanish under refinement.
