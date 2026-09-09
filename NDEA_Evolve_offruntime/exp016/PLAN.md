# Exp016 — regular reconstruction and actual discrete-residual certificates

Status: authorized and in progress; no completion or independent qualification claimed. Exp013–015 are immutable. BASELINE.json records their read-only source/packet audit and exact Exp015 combined-source pin. The startup Git baseline was 8021c836fb6eb43dd18a70fdb71c0e5c147e8a10. The five-module source checkpoint was 2454fac4f3a63e2ad9a6663c8a8f950091dff0ad. The finite-trajectory source checkpoint is ed85977115113da7ca4c4a82b811e21d8965794a (fresh remote readback passed); later current source-bound receipts take precedence. Main is unchanged.

## Chosen architecture and why

Use finite trigonometric spatial synthesis and a quadratic time reconstruction on each time slab. First establish affine-profile derivative/regularity lemmas and exact ordered-stage defect algebra; both have immediate consumers in the quadratic construction. Never assert that a globally stitched piecewise polynomial satisfies Exp015 global classical regularity. Each slab is a globally defined polynomial extension; apply Exp015 separately and accumulate endpoint errors. Endpoint interpolation removes value-jump terms. Variable positive step lengths fit the same local interface.

The accepted quadratic endpoint/derivative/grid-residual identities remove the affine field's leading temporal variation term. The integrated k³/12 temporal residual bound is now development-accepted in QuadraticNorm. OrderedStageAlgebra and OrderedStageBounds now development-prove the ordered eta expansion, retained solve-residual terms, and the explicit induced-operator bounds below. These control the temporal contribution on a fixed grid; a full error rate still requires control of the spatial terms. No O(h²+k²) PDE convergence claim follows. The selected correction uses low-degree polynomial calculus and retains the actual endpoint defect.

A trigonometric/cubic-Hermite time path is another serious option: choosing endpoint slopes from the same static grid generator permits global C1 gluing. It adds gluing/indexing and endpoint-defect residual work. The quadratic slab already supplies a precursor to that construction, so keeping a slabwise theorem does not close the Hermite route. The expanded comparison records this option without changing the chosen endpoint.

The natural experiment boundary is a numerical-to-continuum certificate, including full odd-grid Fourier interpolation/norm fidelity and an actual finite-grid consumer. The full interpolation adapter and actual sampled-potential finite-trajectory certificate are now development-accepted. OneNodeCosine supplies a nonzero variable-potential full-chain control; the legacy constant-potential controls remain separate. Spatial consistency under refinement, and the resulting broader variable-potential convergence theorem, form the next experiment: they require a distinct Fourier aliasing/commutator and discrete-regularity argument. We do not hide that argument inside an assumption that the residual vanishes.

## Exact proposed Exp016 endpoint

1. Grid: N=2M+1 positive odd periodic nodes x_j=j*h, h=2*pi/N, with fiber C² and the existing full-grid EuclideanSpace convention Fin N × Fin2. The first actual legacy instance uses N=n+1 and its existing centered periodic Laplacian; the odd-grid restriction is for the unambiguous centered full Fourier interpolation, not for Cayley wellposedness.
2. Potential: the actual static selfadjoint matrix field V(x), specializing to the Exp014 solution class with second weighted absolute Fourier moments and Hermitian coefficient symmetry. Preserve the old split by A_h=L_h⊗I+I⊗Z and B_h=diag_j(V(x_j)−Z). The old constant V=Z+X reduces to the existing A_h/B_h definitions; prove that identity. General finite Hermitian matrices support the algebra. A sampled-potential approximation is a later explicit extra mismatch, never silently substituted.
3. Scheme: y1=C_A(k/4)y0, y2=C_B(k/2)y1, y3=C_A(k/4)y2, C_G(a)=(I−iaG)(I+iaG)^−1 using the exact existing definition and action order. Positive k; no commutativity assumption. Reuse denominator invertibility, stage uniqueness and unitarity. Retain measured denominator residuals r1,r2,r3 for the inexact-stage interface.
4. Spatial synthesis: S_h y(x)=sum_{m=−M}^M exp(imx) a_m(y), where a_m(y)=N^−1 sum_j exp(−imx_j)y_j. Prove sampling recovers every grid value, actual first/second spatial derivative formulas, periodicity, and ||S_h y||L2=sqrt(h)||y||. This is the faithful norm bridge; no pointwise inverse bound is silently substituted for L2.
5. Time reconstruction: H=A+B, m=(y0+y3)/2, v=(y3−y0)/k, tau=t−(t0+k/2), Q(t)=m+tau*v−(i/2)(tau²−k²/4)H v, w(t,x)=S_h Q(t)(x). Prove endpoints, all Exp015.IsRegularPeriodicField requirements and residual continuity under the actual potential assumptions.
6. Exact discrete defect: eta=(y1+y2)/2−m; d=i*v−H*m. Prove d=(i/k)(r1+r2+r3)+(A/2+B)eta. Exact solves cancel r1/r2/r3, not eta. Preserve AB order in the stronger identity eta=(k²/32)A²(y0+y1+y2+y3)+(k²/8)AB(y1+y2).
7. Actual continuum mismatch: C_h z=S_h(H_h z)−[−partial_xx(S_h z)+V*S_h z]. Prove R_V[w]=S_h d+(i/2)(tau²−k²/4)S_h(H_h²v)+C_h Q(t). This is a derivative identity for the actual reconstruction, not a stipulated forcing.
8. Quantitative slab certificate: on t in[t0,t0+k], prove
   ||R_V[w](t)||L2 <= sqrt(h)(||d||+k²||H²v||/8)+||C_h m||L2+(k/2)||C_h v||L2+(k²/8)||C_h(Hv)||L2.
   The C_h terms are actual spatial consistency expressions, with their exact Fourier/stencil/potential representation exposed. They are not assumed small. The old band consistency hypothesis M*h<=1 fails for the full centered representative band as the grid grows; do not apply those old estimates to every DFT mode. A separate global symbol estimate or frequency split is required for the later refinement proof. For exact Hermitian stages retain graph-norm expressions and prove the coarser fixed-grid bound
   ||d|| <= (k²/16)||A||(||A||+2||B||)²||y0||,
   ||H²v|| <= (||A||+||B||)³||y0||.
   The interval bound follows from k>0 and polynomial inequalities. Sharper integrated constants are optional if low-cost; correctness and reusable structure take precedence.
9. Apply Exp015 to Exp014's actual unique solution, retaining arbitrary initial mismatch ||S_h y_initial−u(0)||L2. For a finite actual trajectory and positive steps, derive endpoint error <= initial error + sum_j k_j*B_j, where B_j is the explicit derived certificate above. Prove needed L2 triangle/norm transfer and slab accumulation. No matching-to-reference initialization hypothesis is inserted.
10. Concrete controls: endpoint recovery, zero step only where division-free algebra permits it, nonzero initial error retained, exact Cayley solves with nonzero macro CN defect, correct factor-order/AB dependence, a constant/finite-mode legacy case recovering existing definitions and bounds. Controls are theorem checks, not substitutes for the general proof.

If a listed submodule proves unexpectedly broad, retain this interface boundary and record a narrower exact accepted endpoint before any seal. Do not silently remove numerical fidelity, norm transfer or the actual Cayley consumer from the experiment.

## Refinement and full convergence: explicit next obligation

The first proposed refinement family is N_q=2(q+1)+1, h_q=2*pi/N_q, T=1, J_q=N_q^4, k_q=1/J_q. This makes the coarse fixed-grid temporal k²*O(h^−6) bound tend to zero if the sampled-potential norm and sqrt(h_q)||y_initial,q|| stay uniformly bounded, which must also be proved. Unitarity propagates the latter bound but does not supply it. The first convergence consumer initializes with actual samples of Exp014 data; prove interpolation convergence and this weighted bound from its Fourier hypotheses. The certificate itself retains arbitrary numerical initial states, and later controlled perturbations add their full initial mismatch. This does not establish the spatial part: C_h acts badly on arbitrary highest-frequency data. A Fourier aliasing/commutator estimate plus suitable uniform discrete regularity, or a rigorous density-and-stability argument, must derive the spatial certificate's vanishing and the initial interpolation error's vanishing.

The follow-on convergence theorem must start from these actual iterates and Exp014-compatible data, prove the initial and accumulated spatial defects tend to zero, then apply the Exp016 certificate. It may first restrict to an explicitly stated stronger weighted Fourier class if required; such added regularity must be written as a new assumption and proved sufficient. We do not claim here that Exp014's second moments imply every higher discrete graph-norm bound, nor that this proposed schedule already closes the proof. The exact first convergence assumptions and rate will be fixed by the spatial argument, not by expected order labels.

This division opens the most immediate reusable proof space: other methods can provide a reconstruction and exact step defect, while reusing regularity, norm transfer, slabwise Exp015 application and initialization handling. Inexact solves, potential approximations and variable steps appear as explicit future consumers. They are opened paths, not all completed theorems.

## Defect obligations and selected route toward refinement

Notation: N=2M+1, h=2*pi/N, k>0; d is the midpoint defect, v=(y3−y0)/k; rho=sqrt(h)*||y0||; a=||A_h||, b=||B_h|| in induced Euclidean operator norm; Vmax=sup_x||V(x)||. The candidate bounds a<=4/h²+1 and b<=Vmax+1 need concrete operator proofs. Here S is actual Fourier interpolation and C_h z=S(H_h z)+partial_xx(S z)−V*S z. No row below assumes its own refinement conclusion.

| Exact contribution | Producing theorem/interface | Assumptions and explicit dependence | Current status and specific refinement obligation |
|---|---|---|---|
| Initial error ||S_h y0−u(0)||L2 | Exp015 residual estimate; SlabError and TargetBinding retain it | Arbitrary numerical y0. For sampled Fourier data and cutoff R resolved by the grid, proposed bound <=2*sqrt(2*pi)*sum_{abs(m)>R}||initialCoeff(m)|| | Retention established in Exp015; actual sampling-tail estimate still needed. Isometry alone does not make initial error vanish. |
| Solve contribution sqrt(h)*sum_j||r_j|| per full slab | Accepted ordered_stage_midpoint_defect; normalized QuadraticCayleyBridge development-accepted | Actual denominator residuals with parameters k/4,k/2,k/4. Division by k in the midpoint defect cancels the slab's k factor | Exact solves specialize r_j=0. Inexact refinement requires a derived accumulated solve budget; no floating-point validation is claimed. |
| Splitting contribution k*sqrt(h)*||(A/2+B)eta|| | OrderedStageAlgebra ordered_internalMeanDefect_exact; OrderedStageBounds orderedCayleySplitDefect_norm_le | Exact Hermitian stages: proved <=rho*k³*a*(a+2b)²/16, with AB order retained. Thus at worst k³ times explicit powers of 4/h²+1 and Vmax+1 | Ordered identity and unitarity-based bounds development-accepted; concrete a/b estimates still needed. Even commuting factors can have nonzero unsplit-CN defect; control development-accepted in QuadraticCayleyBridge. |
| Temporal correction integral sqrt(h)*integral ||c(t) H_h²v|| | Accepted quadraticTime_gridResidual; QuadraticNorm integrated norm bound development-accepted | k³*sqrt(h)*||H_h²v||/12. The exact-stage graph bound ||H²v||<=(a+b)³||y0|| is now development-accepted, giving <=rho*k³*(a+b)³/12 after substitution | Coefficient integral and ordered velocity/operator bounds development-accepted; concrete h/potential operator bounds remain. Fixed-grid k² global error constants grow with h; proposed k=N^-4 only handles this coarse temporal growth after rho/Vmax bounds. |
| Stencil defect C_lap z=S(L_h z)+partial_xx(S z), evaluated at m,v,Hv | SpatialDefectSplit sampledStencilDefect_apply and sampled_spatialDefect_split; StencilFourier fourierCoefficient_gridKinetic, sampledStencilDefect_eq_synthesis and sampledStencilDefect_spatialL2_le accepted | Fourier multiplier delta_l=lambda_h(l)−l². Existing small-band bound abs(delta_l)<=l⁴*h²/8 assumes abs(l)*h<=1; the full band does not satisfy it | FullBandSymbol.modeSymbol_consistency_fullBand proves abs(delta_l)<=h²*l⁴ for every integer l and h>0. StencilFourier now proves the exact multiplier and ||C_lap z||L2 <=sqrt(2*pi)*h²*sqrt(sum_l (l⁴||a_l(z)||)²). This is the actual fourth frequency moment, not an assumed uniform bound. Need control of its numerical evolution/high-frequency tail or a justified smooth-approximation route. L2 isometry and rho bounds do not control derivatives. |
| Potential interpolation/aliasing C_V z=S(P_V z)−V*S z, evaluated at m,v,Hv | SampledCayleyCertificate actual potential matrix/node/stencil identities accepted; SpatialDefectSplit actual interpolation discrepancy and SpatialDefectCertificate finite/partial consumers accepted; Fourier alias sum still pending | Actual sampled V. Coefficients depend on full-grid frequency representatives and convolution aliases. Uniform estimate <=2*Vmax*sqrt(h)*||z|| gives boundedness only, not vanishing | Need smooth-core alias/tail estimates, then uniform potential-perturbation and initialization approximation to transfer convergence. V cutoff must preserve Hermitian Fourier symmetry. |
| Optional potential approximation V_R−V | Later two-potential discrete/continuum perturbation lemmas | deltaV_R<=sum_{abs(l)>R}||potentialCoeff(l)||. Proposed nodal solution perturbation <=T*deltaV_R times the retained initial norm, with no Laplacian norm factor | Reviewed mathematical route, not Lean acceptance. Must prove sampled block norm bound, Cayley perturbation, continuum residual multiplication and uniform cutoff tails. |

For the baseline qualitative target, the selected route to evaluate next is **smooth Fourier approximation plus uniform stability**: first prove actual-scheme convergence for each fixed smooth data/potential cutoff, then transfer it using the mesh-independent potential and initialization perturbation bounds. The smooth-core proof itself still needs propagated regularity/tail estimates for its evolved solution; finite Fourier inputs do not imply an invariant finite solution band. Existing Exp014 assumptions are not silently strengthened. A stronger-data rate theorem, with explicit graph/derivative assumptions and constants, is a separate target.

The development-accepted OneNodeCosine full-pipeline instance uses a one-node odd grid with the actual Z/ sampled-potential-minus-Z split, initial spinor (1,0), and active finite-Fourier scalar potential 2*cos(x)*I. This makes the spatial reconstruction constant but the actual potential residual nonconstant. It checks the concrete interfaces; it is not a refinement theorem and does not replace the general full-grid target. Existing scalar commuting controls remain separate guards.

Achievement labels: INTERFACE PROVED means a checked conditional certificate; ACTUAL SCHEME INSTANTIATED means the real recurrence/reconstruction discharges its conditions; CONVERGENCE PROVED requires the resulting bound to vanish under stated refinements. No structure field may stand in for that numerical proof. The intended certificate is initially analytical: spatial L2 discrepancy terms and infinite-data tails may still require validated quadrature, coefficient-tail bounds and verified arithmetic to become fully computable certified numbers.

## Verification and finish criteria

- Each module checked with pinned Lean, exact source/log/runner hashes, no sorry or extra axioms, explicit audit catalog and unchanged-source checks.
- Independent review of actual statements, recurrence order, assumptions, norm normalization, endpoint conventions and complete defect accounting; meaningful exact controls.
- Reconstruct combined source from pinned predecessors/new modules; isolated local qualification and independent fresh-runtime qualification excluding project artifacts; accepted artifact/source/catalog/transfer checks.
- Finalizer gates bind source, tests, reviews, receipts and packet; read back the sealed packet and verify predecessor baseline unchanged.
- Frequent verified local snapshots; manual saves before long/risky work; source milestone commits on dev/variable-potential with remote readback. Heavy accepted archives belong to the archive layer. A Git checkpoint is not proof qualification.

Startup watcher: tracked session61987, complete output NDEA_Recovery/EXP016_WATCHER.log, interval60seconds/up to12hours. Verified advancing04:07:38→04:08:38UTC. It must be re-established after reboot; no autostart is claimed.

Current target alignment: `design/INDEPENDENT_TARGET_SPEC.md` states the complete intended certificate and refinement quantifiers. `lean/IndependentTarget.lean` imports only sealed numerical definitions; `lean/TargetBinding.lean` now development-proves exact reconstruction agreement, regularity, faithful norm normalization and a derived single/partial-slab Exp014 error certificate. This is not yet the complete concrete sampled-stencil refinement theorem. The bounded external assessment adopted this target discipline; FourierCoefficientBridge now development-proves exact physical-period continuum/DFT coefficient extraction and off-band zero directly from pinned Mathlib with attributed upstream proof-pattern provenance. Its actual reconstruction consumer is accepted; alias-error and coefficient-decay bounds remain separate.

Current concrete consumer (2026-09-09, development acceptance):
`ActualCayleyCertificate` proves grid-time and final-partial-slab accumulation
from the actual recursively computed trajectory. `SampledCayleyCertificate`
then constructs the matrix field of Exp014.operatorPotential via the pinned
matrix/operator equivalence, derives Hermitian samples and the actual centered
stencil identity, and instantiates both certificates without unrelated free
matrices or an assumed compatibility/residual bound. Numerical initial mismatch
and arbitrary positive variable steps remain explicit. These discharge the
finite-trajectory consumer, not the remaining exact Fourier alias/tail control and mesh-uniform refinement. Stronger ordered norm bounds and separate stencil/potential certificate terms are now development-accepted.
The proposed endpoint and qualification gates above are unchanged.

Adversarial source review of spatial refinement: with N=2M+1, M>=1,
V(x)=2*cos(x)*I and the top represented mode exp(i*M*x)u, the potential
interpolation defect is (exp(-i*M*x)-exp(i*(M+1)*x))u, with L2 norm
2*sqrt(pi)*||u|| independent of M. The top-mode stencil defect instead grows
like h^-2. These are reviewed counterexample calculations, not new Lean controls.
They rule out inferring defect vanishing from uniform L2 stability alone, and
support the selected smooth-approximation/tail route. WeightedCoefficientBridge
now supplies the exact continuum coefficient/product-convolution identity needed
to compare against the still-unproved discrete sampling alias sum.

Current quantitative consumer: QuantitativeCayleyCertificate development-proves
sampledCayley_gridTime_quantitative_error and
sampledCayley_partialSlab_quantitative_error using actual ordered stages,
the proven k²*a*(a+2b)²/16 and (a+b)³ temporal constants, and separate
computed stencil/potential L2 terms. No free residual bound or assumed
refinement property enters these theorems. The explicit StencilFourier bound
can estimate each stencil term; the sampled-potential Fourier alias identity
and mesh-uniform evolution/tail control remain the next mathematical links.
