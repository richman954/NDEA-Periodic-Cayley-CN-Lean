import GenericEnergy

/-! Uniqueness within the classical periodic solution class for a common
time- and space-dependent self-adjoint potential and common forcing. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp013

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sq_integral_pos_of_ne_zero (w : ℝ → H) (hw : Continuous w)
    (b L : ℝ) (hL : 0 < L) (hb : w b ≠ 0) :
    0 < ∫ x in b..b+L, ‖w x‖^2 := by
  apply intervalIntegral.integral_pos (by linarith : b < b+L)
    (hw.norm.pow 2).continuousOn
  · intro x hx
    exact sq_nonneg _
  · refine ⟨b, ⟨le_refl _, by linarith⟩, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem norm_sq_integrals_separate_zero (w : ℝ → H) (hw : Continuous w)
    (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖w x‖^2) = 0) : w = 0 := by
  funext x
  by_contra hx
  have hp := norm_sq_integral_pos_of_ne_zero w hw x L hL hx
  rw [hz x] at hp
  exact lt_irrefl 0 hp

theorem norm_sq_integrals_separate (u v : ℝ → H)
    (hu : Continuous u) (hv : Continuous v) (L : ℝ) (hL : 0 < L)
    (hz : ∀ b : ℝ, (∫ x in b..b+L, ‖u x-v x‖^2) = 0) : u = v := by
  have h := norm_sq_integrals_separate_zero (fun x => u x-v x) (hu.sub hv) L hL hz
  funext x
  exact sub_eq_zero.mp (congrFun h x)

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem classical_difference_energy_conserved (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    (∫ x in b..b+L, ‖u s x-v s x‖^2) = ∫ x in b..b+L, ‖u t x-v t x‖^2 :=
  energy_eq (fun r x => u r x-v r x) (classical_sub_same_forcing u v hu hv) hV b s t

theorem classical_unique_at_time (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x))
    (s : ℝ) (hs : ∀ x, u s x = v s x) : u = v := by
  funext t
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  apply norm_sq_integrals_separate (u t) (v t)
    (hu.continuous_solution.comp hp) (hv.continuous_solution.comp hp) L hL
  intro b
  have h := classical_difference_energy_conserved u v hu hv hV b t s
  simpa [hs] using h

theorem classical_unique (hL : 0 < L) (u v : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hv : IsClassicalPeriodicSolution L V f v)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = v 0 x) : u = v :=
  classical_unique_at_time hL u v hu hv hV 0 h0

theorem classical_zero_of_time_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (s : ℝ) (hs : ∀ x, u s x = 0) : u = 0 :=
  classical_unique_at_time hL u 0 hu (classical_zero L V) hV s hs

theorem classical_zero_of_initial_zero (hL : 0 < L) (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (h0 : ∀ x, u 0 x = 0) : u = 0 :=
  classical_zero_of_time_zero hL u hu hV 0 h0

end NDEAEvolve.Exp013
