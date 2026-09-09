import SuperpositionClosure

/-! A concrete growing Fourier cutoff and compatible space/time refinement. -/
noncomputable section
open Filter
open NDEAEvolve.Exp008
namespace NDEAEvolve.Exp009

set_option maxHeartbeats 100000

def cutoff (q : ℕ) : ℕ := q+1
def gridPoints (q : ℕ) : ℕ := 8*(cutoff q)^3
def gridIndex (q : ℕ) : ℕ := gridPoints q-1
def mesh (q : ℕ) : ℝ := 2*Real.pi/(gridPoints q:ℝ)
def timeStep (q : ℕ) : ℝ := 1/(6*(cutoff q:ℝ)^4)
def stepCount (q : ℕ) : ℕ := 6*(cutoff q)^4

theorem cutoff_pos (q : ℕ) : 1 ≤ cutoff q := by simp [cutoff]

theorem cutoff_real_ge_one (q : ℕ) : 1 ≤ (cutoff q:ℝ) := by
  exact_mod_cast cutoff_pos q

theorem gridPoints_pos (q : ℕ) : 0 < gridPoints q := by
  have := cutoff_pos q
  unfold gridPoints
  positivity

theorem gridPoints_eq_gridIndex_succ (q : ℕ) : gridPoints q=gridIndex q+1 := by
  have := gridPoints_pos q
  unfold gridIndex
  omega

theorem cutoff_unaliased (q : ℕ) : 2*cutoff q<gridIndex q+1 := by
  rw [← gridPoints_eq_gridIndex_succ]
  have hm := cutoff_pos q
  have hc : cutoff q ≤ (cutoff q)^3 := le_self_pow₀ hm (by decide)
  unfold gridPoints
  omega

theorem mesh_pos (q : ℕ) : 0 < mesh q := by
  have hp : 0 < (gridPoints q:ℝ) := by exact_mod_cast gridPoints_pos q
  unfold mesh
  positivity

theorem mesh_period (q : ℕ) : ((gridIndex q+1:ℕ):ℝ)*mesh q=2*Real.pi := by
  rw [← gridPoints_eq_gridIndex_succ]
  unfold mesh
  have hp : (gridPoints q:ℝ) ≠ 0 := by exact_mod_cast (gridPoints_pos q).ne'
  field_simp

theorem cutoff_mesh_le_one (q : ℕ) : (cutoff q:ℝ)*mesh q ≤ 1 := by
  have hm := cutoff_real_ge_one q
  have hc : (cutoff q:ℝ) ≤ (cutoff q:ℝ)^3 := le_self_pow₀ hm (by decide)
  have hp : 0 < (8:ℝ)*(cutoff q:ℝ)^3 := by positivity
  simp only [mesh, gridPoints, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hp).2
  have hpi := mul_le_mul_of_nonneg_left Real.pi_le_four (by positivity : 0 ≤ 2*(cutoff q:ℝ))
  linarith only [hpi, hc]

theorem timeStep_pos (q : ℕ) : 0 < timeStep q := by
  have := cutoff_real_ge_one q
  unfold timeStep
  positivity

theorem timeStep_nonneg (q : ℕ) : 0 ≤ timeStep q := (timeStep_pos q).le

theorem timeStep_restriction (q : ℕ) :
    2*timeStep q*((cutoff q:ℝ)^2+2) ≤ 1 := by
  have hm := cutoff_real_ge_one q
  have hsq : 1 ≤ (cutoff q:ℝ)^2 := one_le_pow₀ hm
  have hfour : (cutoff q:ℝ)^2 ≤ (cutoff q:ℝ)^4 := pow_le_pow_right₀ hm (by decide)
  have hp : 0 < (6:ℝ)*(cutoff q:ℝ)^4 := by positivity
  change 2*(1/(6*(cutoff q:ℝ)^4))*((cutoff q:ℝ)^2+2) ≤ 1
  rw [mul_one_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).2
  linarith only [hsq, hfour]

theorem stepCount_timeStep (q : ℕ) : (stepCount q:ℝ)*timeStep q=1 := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  simp only [stepCount, timeStep, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp

theorem cutoff_tendsto_atTop : Tendsto cutoff atTop atTop := tendsto_add_atTop_nat 1

theorem cutoff_inverse_tendsto_zero :
    Tendsto (fun q => (cutoff q:ℝ)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_nhds_zero_nat.comp cutoff_tendsto_atTop

theorem mesh_eq_inverse (q : ℕ) :
    mesh q = (Real.pi/4)*((cutoff q:ℝ)⁻¹)^3 := by
  simp only [mesh, gridPoints, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem timeStep_eq_inverse (q : ℕ) :
    timeStep q = (1/6:ℝ)*((cutoff q:ℝ)⁻¹)^4 := by
  unfold timeStep
  ring

theorem mesh_tendsto_zero : Tendsto mesh atTop (nhds 0) := by
  have h := (cutoff_inverse_tendsto_zero.pow 3).const_mul (Real.pi/4)
  simpa only [← mesh_eq_inverse, zero_pow (by omega : 3 ≠ 0), mul_zero] using h

theorem timeStep_tendsto_zero : Tendsto timeStep atTop (nhds 0) := by
  have h := (cutoff_inverse_tendsto_zero.pow 4).const_mul (1/6:ℝ)
  simpa only [← timeStep_eq_inverse, zero_pow (by omega : 4 ≠ 0), mul_zero] using h

theorem cutoff_error_eq_inverse (q : ℕ) :
    Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2 =
      ((1000/36:ℝ)*(1+2*((cutoff q:ℝ)⁻¹)^2)^3+Real.pi^2/128)*
        ((cutoff q:ℝ)⁻¹)^2 := by
  have hm : (cutoff q:ℝ) ≠ 0 := by have := cutoff_real_ge_one q; linarith
  rw [mesh_eq_inverse, timeStep_eq_inverse]
  unfold Ct Cs
  field_simp
  ring

theorem cutoff_error_tendsto_zero :
    Tendsto (fun q => Ct (cutoff q)*(timeStep q)^2+Cs (cutoff q)*(mesh q)^2)
      atTop (nhds 0) := by
  have hz := cutoff_inverse_tendsto_zero.pow 2
  have ha := (((tendsto_const_nhds (x := (1:ℝ))).add (hz.const_mul 2)).pow 3).const_mul (1000/36:ℝ)
  have hb := (ha.add_const (Real.pi^2/128)).mul hz
  simpa only [← cutoff_error_eq_inverse, zero_pow (by omega : 2 ≠ 0), mul_zero] using hb

/- Exact controls: the cutoff really grows, and the first schedule is admissible. -/
theorem control_cutoff_strict (q : ℕ) : cutoff q<cutoff (q+1) := by simp [cutoff]

theorem control_first_schedule :
    cutoff 0=1 ∧ gridPoints 0=8 ∧ gridIndex 0=7 ∧ stepCount 0=6 ∧ timeStep 0=1/6 := by
  norm_num [cutoff, gridPoints, gridIndex, stepCount, timeStep]

#print axioms cutoff_pos
#print axioms cutoff_real_ge_one
#print axioms gridPoints_pos
#print axioms gridPoints_eq_gridIndex_succ
#print axioms cutoff_unaliased
#print axioms mesh_pos
#print axioms mesh_period
#print axioms cutoff_mesh_le_one
#print axioms timeStep_pos
#print axioms timeStep_nonneg
#print axioms timeStep_restriction
#print axioms stepCount_timeStep
#print axioms cutoff_tendsto_atTop
#print axioms cutoff_inverse_tendsto_zero
#print axioms mesh_eq_inverse
#print axioms timeStep_eq_inverse
#print axioms mesh_tendsto_zero
#print axioms timeStep_tendsto_zero
#print axioms cutoff_error_eq_inverse
#print axioms cutoff_error_tendsto_zero
#print axioms control_cutoff_strict
#print axioms control_first_schedule

end NDEAEvolve.Exp009
