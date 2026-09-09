import ClassicalUniqueness

/-! Exact controls for classical uniqueness. A nonzero frequency-one solution
and the zero solution distinguish the initial-data hypothesis from merely
sharing a PDE. Terminal matching also tests recovery at an earlier time. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp012.Controls

def oneModeCoefficients (m : ℤ) : E 2 :=
  if m = 1 then Exp007.Controls.initialSpinor else 0

def oneModeSolution : ℝ → ℝ → E 2 := infiniteSolution oneModeCoefficients

theorem one_mode_regular : Regular oneModeCoefficients := by
  have he : (fun m : ℤ => frequencyWeight 2 m * ‖oneModeCoefficients m‖) =
      (fun m : ℤ => if m = 1 then frequencyWeight 2 1 * ‖Exp007.Controls.initialSpinor‖ else 0) := by
    funext m
    by_cases hm : m = 1 <;> simp [oneModeCoefficients, hm]
  unfold Regular
  rw [he]
  exact (hasSum_ite_eq (1 : ℤ) _).summable

theorem one_mode_support_singleton : Function.support oneModeCoefficients = {1} := by
  have hv : Exp007.Controls.initialSpinor ≠ 0 := norm_ne_zero_iff.mp (by
    rw [Exp007.Controls.initialSpinor_norm]
    norm_num)
  ext m
  by_cases hm : m = 1 <;> simp [Function.mem_support, oneModeCoefficients, hm, hv]

theorem one_mode_solution_eq (t x : ℝ) :
    oneModeSolution t x = modeSolution 1 Exp007.Controls.initialSpinor t x := by
  unfold oneModeSolution infiniteSolution
  rw [tsum_eq_single (1 : ℤ)]
  · simp [oneModeCoefficients]
  · intro m hm
    simp [oneModeCoefficients, hm, modeSolution, modeOrbit]

theorem one_mode_classical : IsClassicalPeriodicSolution oneModeSolution :=
  infiniteSolution_classical oneModeCoefficients one_mode_regular

theorem one_mode_norm_one (t x : ℝ) : ‖oneModeSolution t x‖ = 1 := by
  rw [one_mode_solution_eq, modeSolution_norm, Exp007.Controls.initialSpinor_norm]

/-- Two classical solutions of this same PDE differ when their data differ. -/
theorem initial_data_cannot_be_omitted :
    ∃ u v : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧
      IsClassicalPeriodicSolution v ∧ u 0 0 ≠ v 0 0 ∧ u ≠ v := by
  have hne : oneModeSolution 0 0 ≠ 0 := by
    intro h
    have hn := one_mode_norm_one 0 0
    rw [h, norm_zero] at hn
    norm_num at hn
  refine ⟨oneModeSolution, 0, one_mode_classical, classical_zero, hne, ?_⟩
  intro he
  exact hne (congrFun (congrFun he 0) 0)

theorem one_mode_energy (b t : ℝ) : energy oneModeSolution b t = 2 * Real.pi := by
  unfold energy
  simp_rw [one_mode_norm_one, one_pow]
  simp

theorem zero_data_unique :
    ∃! u : ℝ → ℝ → E 2, IsClassicalPeriodicSolution u ∧ ∀ x, u 0 x = 0 := by
  refine ⟨0, ⟨classical_zero, fun _ => rfl⟩, ?_⟩
  intro u hu
  exact classical_zero_of_initial_zero u hu.1 hu.2

/-- Matching the nonzero solution at time one recovers its earlier initial
profile. The competing classical solution is an arbitrary function. -/
theorem terminal_match_recovers_initial (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (h1 : ∀ x, u 1 x = oneModeSolution 1 x) (x : ℝ) :
    u 0 x = Exp006.phase x • Exp007.Controls.initialSpinor := by
  have he := classical_unique_at_time u oneModeSolution hu one_mode_classical 1 h1
  calc
    _ = oneModeSolution 0 x := congrFun (congrFun he 0) x
    _ = _ := by rw [one_mode_solution_eq]; simp

/-- The chosen convention is `density_t = flux_x`: frequency +1 has flux -2. -/
theorem one_mode_flux_sign : flux oneModeSolution 0 0 = -2 := by
  have hvalue : oneModeSolution 0 0 = Exp007.Controls.initialSpinor := by
    rw [one_mode_solution_eq]
    simp
  have hfun : oneModeSolution 0 = modeSolution 1 Exp007.Controls.initialSpinor 0 :=
    funext (one_mode_solution_eq 0)
  have hd : deriv (oneModeSolution 0) 0 = Complex.I • Exp007.Controls.initialSpinor := by
    rw [hfun, (modeSolution_space_hasDerivAt 1 Exp007.Controls.initialSpinor 0 0).deriv]
    simp
  unfold flux
  rw [hvalue, hd, smul_smul, Complex.I_mul_I, neg_one_smul, inner_neg_right,
    inner_self_eq_norm_sq_to_K, Exp007.Controls.initialSpinor_norm]
  norm_num

end NDEAEvolve.Exp012.Controls
