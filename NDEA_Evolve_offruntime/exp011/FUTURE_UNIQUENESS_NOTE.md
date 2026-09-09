# Candidate later milestone: uniqueness in the full classical class

Experiment 011 selects convergence of an explicitly reconstructed numerical
field. Uniqueness of the classical PDE solution remains a separate task.

A feasible route for the current constant Hermitian spin potential is the
energy method. It would compare arbitrary functions satisfying Experiment
010's `IsClassicalPeriodicSolution`, without assuming that a competing
solution already has the proved Fourier-series representation.

For any real base point `a`, define

\[
E_a(t)=\int_a^{a+2\pi}\|u(t,x)\|^2\,dx,
\qquad J(t,x)=2\operatorname{Re}\langle u(t,x),iU_x(t,x)\rangle.
\]

The intended local identity is `∂t ‖u‖² = ∂x J`. Hermitian symmetry cancels
the potential contribution, and `Re ⟨Ux,i Ux⟩=0` cancels the other flux term.
Periodicity of the first spatial derivative follows by differentiating the
actual periodicity identity for `u`.

The pinned Mathlib has the required principal APIs:

- `HasDerivAt.norm_sq`, `HasDerivAt.inner`, and
  `LinearMap.IsSymmetric.im_inner_self_apply` for the local identity.
- `IsCompact.exists_bound_of_continuousOn` and
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  for differentiation of the energy integral. Joint continuity on a compact
  time-space rectangle supplies the local integrable constant majorant; no
  global-in-time boundedness premise needs to be added to the classical class.
- The interval-integral fundamental theorem for the flux derivative, followed
  by `is_const_of_deriv_eq_zero`, for energy conservation.
- `intervalIntegral.integral_pos` for recovering pointwise equality from zero
  energy and continuity. Permitting an arbitrary interval base avoids quotient
  representatives or reducing an arbitrary point modulo the period.

After proving closure of the classical predicate under subtraction, the
target theorem is:

```lean
theorem classical_unique
    (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u)
    (hv : IsClassicalPeriodicSolution v)
    (h0 : ∀ x, u 0 x = v 0 x) : u = v
```

The difference has zero initial energy, hence zero energy at every time.
Any nonzero value would give a positive integral on a period interval,
contradicting conservation. A corollary would identify any classical solution
with the existing infinite Fourier solution whenever their initial values
agree and the Fourier data satisfy `Regular`.

This is an API and mathematical feasibility assessment, not a checked
uniqueness proof. The exploratory `lean/probes/ProbeEnergy.lean` compile was
interrupted after reconstruction was selected, to release the shared Lean
lock. Its receipt records exit 130 and no success claim. The probe is excluded
from the Experiment 011 production proof.
