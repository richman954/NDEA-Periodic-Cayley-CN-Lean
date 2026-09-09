import ClassicalClosure

/-! A bound uniform over every time step of the existing refinement schedule.
The weighted error is converted to a nodal norm estimate that still tends to
zero, despite the factor inverse square root of the mesh spacing. -/
noncomputable section
open Filter
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
open NDEAEvolve.Exp010 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp011

def scheduleCoefficient (q : ℕ) : ℝ :=
  (1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128+2

def nodalBound (q : ℕ) (a : ℤ → E 2) : ℝ :=
  moment 2 a * scheduleCoefficient q * Real.sqrt (8*(cutoff q:ℝ)⁻¹)

theorem scheduleCoefficient_nonneg (q : ℕ) : 0 ≤ scheduleCoefficient q := by
  unfold scheduleCoefficient
  positivity

theorem nodalBound_nonneg (q : ℕ) (a : ℤ → E 2) : 0 ≤ nodalBound q a :=
  mul_nonneg (mul_nonneg (moment_nonneg 2 a) (scheduleCoefficient_nonneg q))
    (Real.sqrt_nonneg _)

theorem scheduled_moment_tail_bound (q : ℕ) (a : ℤ → E 2) :
    moment 2 a / ((cutoff q:ℝ)+1)^2 ≤ moment 2 a*((cutoff q:ℝ)⁻¹)^2 := by
  have hm := cutoff_real_ge_one q
  have hp : 0 < (cutoff q:ℝ)^2 := by positivity
  have hd : (cutoff q:ℝ)^2 ≤ ((cutoff q:ℝ)+1)^2 := by nlinarith
  simpa only [div_eq_mul_inv, inv_pow] using
    div_le_div_of_nonneg_left (moment_nonneg 2 a) hp hd

theorem scheduled_sqrt_ratio (q : ℕ) :
    Real.sqrt (2*Real.pi)*((cutoff q:ℝ)⁻¹)^2 / Real.sqrt (mesh q) =
      Real.sqrt (8*(cutoff q:ℝ)⁻¹) := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  have hr : 0 ≤ (cutoff q:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),
    Real.sq_sqrt (mesh_pos q).le, Real.sq_sqrt (by positivity : 0 ≤ 8*(cutoff q:ℝ)⁻¹),
    mesh_eq_inverse]
  field_simp [Real.pi_ne_zero, hm]
  <;> ring

theorem all_steps_weighted_error_bound (q j : ℕ) (hj : j ≤ stepCount q)
    (a : ℤ → E 2) (ha : Regular a) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) j a
      (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) ≤
        Real.sqrt (2*Real.pi)*moment 2 a*scheduleCoefficient q*((cutoff q:ℝ)⁻¹)^2 := by
  have ht : (j:ℝ)*timeStep q ≤ 1 := by
    calc
      _ ≤ (stepCount q:ℝ)*timeStep q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (timeStep_nonneg q)
      _ = _ := stepCount_timeStep q
  have hb := (classical_grid_error_bound (cutoff q) (gridIndex q)
    (mesh q) (timeStep q) 1 j a
    (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) ha
    (cutoff_pos q) (cutoff_unaliased q) (mesh_period q) (mesh_pos q)
    (cutoff_mesh_le_one q) (timeStep_nonneg q) (timeStep_restriction q) ht).2
  simp only [classicalInitialError, sub_self, norm_zero, mul_zero, zero_add, one_mul] at hb
  have hc : 0 ≤ Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2 :=
    add_nonneg (mul_nonneg (Ct_nonneg _) (sq_nonneg _))
      (mul_nonneg (Cs_nonneg _) (sq_nonneg _))
  have hmass := mul_le_mul_of_nonneg_left (mass_le_moment 2 a ha) hc
  have htail := mul_le_mul_of_nonneg_left (scheduled_moment_tail_bound q a)
    (by norm_num : (0:ℝ) ≤ 2)
  apply hb.trans
  calc
    _ ≤ Real.sqrt (2*Real.pi)*
        ((Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)*moment 2 a +
          2*(moment 2 a*((cutoff q:ℝ)⁻¹)^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hmass htail) (Real.sqrt_nonneg _)
    _ = _ := by rw [cutoff_error_eq_inverse]; unfold scheduleCoefficient; ring

theorem all_steps_nodal_bound (q j : ℕ) (hj : j ≤ stepCount q)
    (a : ℤ → E 2) (ha : Regular a) :
    classicalGridError (gridIndex q) (mesh q) (timeStep q) j a
      (sampleSolution (gridIndex q) (mesh q) (infiniteSolution a) 0) /
        Real.sqrt (mesh q) ≤ nodalBound q a := by
  apply (div_le_div_of_nonneg_right (all_steps_weighted_error_bound q j hj a ha)
    (Real.sqrt_nonneg _)).trans
  have he : Real.sqrt (2*Real.pi)*moment 2 a*scheduleCoefficient q*((cutoff q:ℝ)⁻¹)^2 /
      Real.sqrt (mesh q) = moment 2 a*scheduleCoefficient q*
        (Real.sqrt (2*Real.pi)*((cutoff q:ℝ)⁻¹)^2 / Real.sqrt (mesh q)) := by ring
  rw [he, scheduled_sqrt_ratio]
  exact le_refl _

theorem scheduleCoefficient_tendsto :
    Tendsto scheduleCoefficient atTop (nhds ((1000/36:ℝ)+Real.pi^2/128+2)) := by
  have h := ((((cutoff_inverse_tendsto_zero.pow 2).const_mul 2).const_add 1).pow 3).const_mul
    (1000/36:ℝ)
  change Tendsto (fun q => (1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128+2)
    atTop (nhds ((1000/36:ℝ)+Real.pi^2/128+2))
  simpa using (h.add_const (Real.pi^2/128)).add_const 2

theorem nodalBound_tendsto_zero (a : ℤ → E 2) :
    Tendsto (fun q => nodalBound q a) atTop (nhds 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (cutoff_inverse_tendsto_zero.const_mul 8)
  simpa [nodalBound] using (scheduleCoefficient_tendsto.const_mul (moment 2 a)).mul hs

end NDEAEvolve.Exp011
