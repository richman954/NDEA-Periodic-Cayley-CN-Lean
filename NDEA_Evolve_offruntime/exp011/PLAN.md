# Experiment 011 — reconstructed space-time convergence

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

Keep Experiment 010 and all earlier sealed files unchanged. The new milestone
constructs an actual numerical spinor field from the grid iterates and proves
uniform convergence throughout `[0,1] × [0,2π]` to the classical infinite
Fourier solution of `iUt=-Uxx+(Z+X)U`.

The coefficient assumption remains `Σ_m(1+|m|)² ‖a_m‖<∞`. Initialization is
exact sampling of the full infinite reference. The schedule remains
`M=q+1`, `d=8M³`, `h=2π/d`, `k=1/(6M⁴)`, `N=6M⁴`, so `Nk=1`.

Define the reconstruction explicitly by clamping the spatial cell index
`floor(x/h)` to `d−1` and the temporal index `floor(t/k)` to `N`.
Extract both spin components of the actual numerical state at that node and
step. At `x=2π`, the reconstruction takes the last grid node; the estimate
includes the resulting spatial error. Finite reconstructed fields need not
have exactly equal endpoint values or be continuous. The limit is periodic
and classical.

Acceptance requires:

1. Derive global space/time norm difference bounds for the actual classical
   reference, with constants `A₂` and `2A₂`.
2. Prove the explicit index bounds, spinor extraction contraction, and the
   reconstruction estimate `e_grid(j)/sqrt(h)+A₂*h+2A₂*k`.
3. Bound every scheduled numerical step using the existing weighted theorem;
   show the divided grid error tends to zero. With `r=1/M`, a sufficient
   nodal bound is
   `A₂*[(1000/36)*(1+2r²)^3+π²/128+2]*sqrt(8r)`.
4. Prove uniform convergence of the actual reconstructed field on the entire
   closed space-time rectangle, together with its classical target predicate.
5. Check exact controls and supporting reconstruction numerics, all modules,
   the complete new public theorem catalog in a combined source, and an
   independent final check on a fresh Colab CPU VM. Validate transferred
   evidence and seal a checksum-verified packet.

The bound is conservative. No sharp uniform convergence rate, arbitrary
initial weighted-error extension, uniqueness theorem, variable spatial
potential, or general PDE claim is included. The independent checks retain
the documented trust in the pinned compiler and compatible external library
artifacts; project artifacts are excluded from combined import paths.
