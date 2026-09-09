import GenericUniqueness
import ClassicalUniqueness

/-! Exact specialization of the generic framework to the previously verified
spinor model, including its unique numerical limit. -/
noncomputable section
open Filter
open NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010 NDEAEvolve.Exp011
namespace NDEAEvolve.Exp013

def legacyPotential (_t _x : ℝ) : E 2 →L[ℂ] E 2 :=
  operatorOf (Exp007.Z + Exp007.X)

theorem legacyPotential_selfadjoint (t x : ℝ) :
    IsSelfAdjoint (legacyPotential t x) := Exp012.potential_selfadjoint

theorem legacy_classical_iff (u : ℝ → ℝ → E 2) :
    IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u ↔
      Exp010.IsClassicalPeriodicSolution u := by
  constructor
  · intro hu
    exact {
      time_differentiable := hu.time_differentiable
      space_differentiable := hu.space_differentiable
      second_space_differentiable := hu.second_space_differentiable
      continuous_solution := hu.continuous_solution
      continuous_time_derivative := hu.continuous_time_derivative
      continuous_space_derivative := hu.continuous_space_derivative
      continuous_second_derivative := hu.continuous_second_derivative
      periodic := hu.periodic
      schrodinger := fun t x => by simpa [legacyPotential] using hu.schrodinger t x }
  · intro hu
    exact {
      time_differentiable := hu.time_differentiable
      space_differentiable := hu.space_differentiable
      second_space_differentiable := hu.second_space_differentiable
      continuous_solution := hu.continuous_solution
      continuous_time_derivative := hu.continuous_time_derivative
      continuous_space_derivative := hu.continuous_space_derivative
      continuous_second_derivative := hu.continuous_second_derivative
      periodic := hu.periodic
      schrodinger := fun t x => by simpa [legacyPotential] using hu.schrodinger t x }

theorem legacy_unique_via_generic (u v : ℝ → ℝ → E 2)
    (hu : Exp010.IsClassicalPeriodicSolution u) (hv : Exp010.IsClassicalPeriodicSolution v)
    (s : ℝ) (hs : ∀ x, u s x = v s x) : u = v :=
  classical_unique_at_time (by positivity) u v
    ((legacy_classical_iff u).mpr hu) ((legacy_classical_iff v).mpr hv)
    legacyPotential_selfadjoint s hs

theorem legacy_eq_infiniteSolution (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : Exp010.IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x) : u = infiniteSolution a :=
  legacy_unique_via_generic u (infiniteSolution a) hu (infiniteSolution_classical a ha) 0 h0

theorem legacy_existsUnique_via_generic (a : ℤ → E 2) (ha : Regular a) :
    ∃! u : ℝ → ℝ → E 2,
      IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u ∧
      ∀ x, u 0 x = infiniteSolution a 0 x := by
  refine ⟨infiniteSolution a,
    ⟨(legacy_classical_iff _).mpr (infiniteSolution_classical a ha), fun _ => rfl⟩, ?_⟩
  intro u hu
  exact legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu.1) hu.2

theorem legacy_reconstruction_converges (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x) :
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => u p.1 p.2) atTop spaceTimeDomain := by
  rw [legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu) h0]
  exact reconstruction_tendstoUniformlyOn a ha

theorem legacy_reconstruction_error (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution (2 * Real.pi) legacyPotential 0 u)
    (h0 : ∀ x, u 0 x = infiniteSolution a 0 x)
    (t x : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖scheduledReconstruction q a t x - u t x‖ ≤ uniformBound q a := by
  rw [legacy_eq_infiniteSolution a ha u ((legacy_classical_iff u).mp hu) h0]
  exact scheduled_reconstruction_error_bound q a ha t x ht hx

end NDEAEvolve.Exp013
