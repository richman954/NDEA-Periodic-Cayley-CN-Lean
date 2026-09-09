import EnergyConservation
import EnergySeparation
import UniformConvergence

/-! Uniqueness for arbitrary classical periodic functions, and identification
of the previously reconstructed numerical limit with that unique solution. -/
noncomputable section
open MeasureTheory Filter
open NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010 NDEAEvolve.Exp011
namespace NDEAEvolve.Exp012

theorem classical_difference_energy_conserved (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (b s t : ℝ) :
    (∫ x in b..b+2*Real.pi, ‖u s x-v s x‖^2) =
      ∫ x in b..b+2*Real.pi, ‖u t x-v t x‖^2 :=
  energy_eq (fun r x => u r x-v r x) (classical_sub u v hu hv) b s t

theorem classical_unique_at_time (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (s : ℝ) (hs : ∀ x, u s x=v s x) : u=v := by
  funext t
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  apply norm_sq_integrals_separate (u t) (v t)
    (hu.continuous_solution.comp hp) (hv.continuous_solution.comp hp)
    (2*Real.pi) (by positivity)
  intro b
  have h := classical_difference_energy_conserved u v hu hv b t s
  simpa [hs] using h

theorem classical_unique (u v : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (hv : IsClassicalPeriodicSolution v)
    (h0 : ∀ x, u 0 x=v 0 x) : u=v :=
  classical_unique_at_time u v hu hv 0 h0

theorem classical_zero_of_initial_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (h0 : ∀ x, u 0 x=0) : u=0 :=
  classical_unique u 0 hu classical_zero h0

theorem classical_eq_infiniteSolution (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x) : u=infiniteSolution a :=
  classical_unique u (infiniteSolution a) hu (infiniteSolution_classical a ha) h0

theorem classical_existsUnique (a : ℤ → E 2) (ha : Regular a) :
    ∃! u : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧
      ∀ x, u 0 x=infiniteSolution a 0 x := by
  refine ⟨infiniteSolution a, ⟨infiniteSolution_classical a ha, fun _ => rfl⟩, ?_⟩
  intro u hu
  exact classical_eq_infiniteSolution a ha u hu.1 hu.2

theorem reconstruction_converges_to_classical (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x) :
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => u p.1 p.2) atTop spaceTimeDomain := by
  rw [classical_eq_infiniteSolution a ha u hu h0]
  exact reconstruction_tendstoUniformlyOn a ha

theorem reconstruction_error_to_classical (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (h0 : ∀ x, u 0 x=infiniteSolution a 0 x)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    ‖scheduledReconstruction q a t x-u t x‖ ≤ uniformBound q a := by
  rw [classical_eq_infiniteSolution a ha u hu h0]
  exact scheduled_reconstruction_error_bound q a ha t x ht hx

end NDEAEvolve.Exp012
