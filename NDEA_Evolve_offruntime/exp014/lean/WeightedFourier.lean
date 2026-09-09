import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A complete all-mode Fourier state space. Its coordinates store the second
weighted coefficients, so completeness is inherited from Mathlib's ℓ¹ space.
The free Schrödinger flow is an isometry and is jointly continuous in time and
state; operator-norm continuity of the flow is not asserted. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

abbrev FourierState (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℤ => H) 1

def weight (m : ℤ) : ℝ := (1 + |(m : ℝ)|)^2

theorem weight_one_le (m : ℤ) : 1 ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ)]

theorem weight_pos (m : ℤ) : 0 < weight m := lt_of_lt_of_le zero_lt_one (weight_one_le m)

theorem weight_ge_one (m : ℤ) : 1 ≤ weight m := weight_one_le m

theorem abs_frequency_le_weight (m : ℤ) : |(m : ℝ)| ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ), sq_nonneg |(m : ℝ)|]

theorem frequency_sq_le_weight (m : ℤ) : (m : ℝ)^2 ≤ weight m := by
  unfold weight
  nlinarith [abs_nonneg (m : ℝ), sq_abs (m : ℝ)]

theorem abs_frequency_div_weight_le (m : ℤ) : |(m : ℝ)| / weight m ≤ 1 := by
  exact (div_le_one (weight_pos m)).mpr (abs_frequency_le_weight m)

theorem frequency_sq_div_weight_le (m : ℤ) : (m : ℝ)^2 / weight m ≤ 1 := by
  exact (div_le_one (weight_pos m)).mpr (frequency_sq_le_weight m)

theorem weight_add_le (m n : ℤ) : weight (m+n) ≤ weight m * weight n := by
  have habs : |((m+n : ℤ) : ℝ)| ≤ |(m : ℝ)| + |(n : ℝ)| := by
    simpa using abs_add_le (m : ℝ) (n : ℝ)
  have hbase : 1 + |((m+n : ℤ) : ℝ)| ≤ (1+|(m : ℝ)|)*(1+|(n : ℝ)|) := by
    nlinarith [abs_nonneg (m : ℝ), abs_nonneg (n : ℝ),
      mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg (n : ℝ))]
  unfold weight
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hbase 2

theorem weight_neg (m : ℤ) : weight (-m) = weight m := by simp [weight]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def coefficient (b : FourierState H) (m : ℤ) : H :=
  (((weight m)⁻¹ : ℝ) : ℂ) • b m

def coefficientCLM (m : ℤ) : FourierState H →L[ℂ] H :=
  (((weight m)⁻¹ : ℝ) : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => H) 1 m

theorem coefficientCLM_apply (m : ℤ) (b : FourierState H) :
    coefficientCLM m b = coefficient b m := rfl

omit [NormedSpace ℂ H] in
theorem state_summable_norm (b : FourierState H) : Summable (fun m : ℤ => ‖b m‖) := by
  simpa using (lp.memℓp b).summable (by norm_num : 0 < (1 : ENNReal).toReal)

omit [NormedSpace ℂ H] in
theorem state_tsum_norm (b : FourierState H) : (∑' m : ℤ, ‖b m‖) = ‖b‖ := by
  simpa using (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) b).symm

theorem coefficient_norm (b : FourierState H) (m : ℤ) :
    ‖coefficient b m‖ = (weight m)⁻¹ * ‖b m‖ := by
  simp only [coefficient, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (weight_pos m).le)]

theorem weight_mul_coefficient_norm (b : FourierState H) (m : ℤ) :
    weight m * ‖coefficient b m‖ = ‖b m‖ := by
  rw [coefficient_norm, ← mul_assoc, mul_inv_cancel₀ (weight_pos m).ne', one_mul]

theorem weighted_summable (b : FourierState H) :
    Summable (fun m : ℤ => weight m * ‖coefficient b m‖) := by
  simpa only [weight_mul_coefficient_norm] using state_summable_norm b

theorem weighted_tsum_norm (b : FourierState H) :
    (∑' m : ℤ, weight m * ‖coefficient b m‖) = ‖b‖ := by
  simpa only [weight_mul_coefficient_norm] using state_tsum_norm b

def ofCoefficients (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) : FourierState H :=
  ⟨fun m => (weight m : ℂ) • a m, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (weight_pos _).le] using ha⟩

theorem ofCoefficients_apply (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) (m : ℤ) :
    ofCoefficients a ha m = (weight m : ℂ) • a m := rfl

theorem coefficient_ofCoefficients (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) (m : ℤ) :
    coefficient (ofCoefficients a ha) m = a m := by
  rw [coefficient, ofCoefficients_apply, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (weight_pos m).ne', Complex.ofReal_one, one_smul]

theorem ofCoefficients_norm (a : ℤ → H)
    (ha : Summable (fun m : ℤ => weight m * ‖a m‖)) :
    ‖ofCoefficients a ha‖ = ∑' m : ℤ, weight m * ‖a m‖ := by
  simpa only [coefficient_ofCoefficients] using (weighted_tsum_norm (ofCoefficients a ha)).symm

theorem coefficient_summable_norm (b : FourierState H) :
    Summable (fun m : ℤ => ‖coefficient b m‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (weight_one_le m)
      (norm_nonneg (coefficient b m))) (weighted_summable b)

theorem coefficient_summable [CompleteSpace H] (b : FourierState H) :
    Summable (coefficient b) := (coefficient_summable_norm b).of_norm

def phase (t : ℝ) (m : ℤ) : ℂ := Complex.exp (-Complex.I * (m : ℂ)^2 * (t : ℂ))

theorem phase_norm (t : ℝ) (m : ℤ) : ‖phase t m‖ = 1 := by
  simp [phase, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem phase_zero (m : ℤ) : phase 0 m = 1 := by simp [phase]

theorem phase_add (s t : ℝ) (m : ℤ) : phase (s+t) m = phase s m * phase t m := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phase_continuous (m : ℤ) : Continuous (fun t : ℝ => phase t m) := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem phase_hasDerivAt (t : ℝ) (m : ℤ) :
    HasDerivAt (fun s : ℝ => phase s m) ((-Complex.I*(m : ℂ)^2) * phase t m) t := by
  have hd : HasDerivAt (fun s : ℝ => (-Complex.I*(m : ℂ)^2)*(s : ℂ))
      (-Complex.I*(m : ℂ)^2) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using!
      ((hasDerivAt_id t).ofReal_comp.const_mul (-Complex.I*(m : ℂ)^2))
  simpa only [phase, mul_comm] using! hd.cexp

def freeFlowLinear (t : ℝ) : FourierState H →ₗ[ℂ] FourierState H where
  toFun b := ⟨fun m => phase t m • b m, (lp.memℓp b).mono' (fun m => by
    simp only [norm_smul, phase_norm, one_mul, le_refl])⟩
  map_add' b c := by
    apply lp.ext
    funext m
    exact smul_add (phase t m) (b m) (c m)
  map_smul' c b := by
    apply lp.ext
    funext m
    exact smul_comm (phase t m) c (b m)

theorem freeFlowLinear_apply (t : ℝ) (b : FourierState H) (m : ℤ) :
    freeFlowLinear t b m = phase t m • b m := rfl

theorem freeFlowLinear_norm (t : ℝ) (b : FourierState H) : ‖freeFlowLinear t b‖ = ‖b‖ := by
  rw [← state_tsum_norm, ← state_tsum_norm]
  simp only [freeFlowLinear_apply, norm_smul, phase_norm, one_mul]

def freeFlow (t : ℝ) : FourierState H →L[ℂ] FourierState H :=
  (freeFlowLinear t).mkContinuous 1 (fun b => by simp [freeFlowLinear_norm])

theorem freeFlow_apply (t : ℝ) (b : FourierState H) (m : ℤ) :
    freeFlow t b m = phase t m • b m := rfl

theorem freeFlow_norm (t : ℝ) (b : FourierState H) : ‖freeFlow t b‖ = ‖b‖ :=
  freeFlowLinear_norm t b

theorem freeFlow_opNorm_le (t : ℝ) : ‖freeFlow (H := H) t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun b => by simp [freeFlow_norm])

theorem freeFlow_zero (b : FourierState H) : freeFlow 0 b = b := by
  apply lp.ext
  funext m
  simp only [freeFlow_apply, phase_zero, one_smul]

theorem freeFlow_add (s t : ℝ) (b : FourierState H) :
    freeFlow (s+t) b = freeFlow s (freeFlow t b) := by
  apply lp.ext
  funext m
  simp only [freeFlow_apply, phase_add, smul_smul]

theorem freeFlow_neg_cancel (t : ℝ) (b : FourierState H) :
    freeFlow (-t) (freeFlow t b) = b := by
  rw [← freeFlow_add, neg_add_cancel, freeFlow_zero]

theorem freeFlow_isometry (t : ℝ) : Isometry (freeFlow (H := H) t) := by
  apply isometry_iff_dist_eq.mpr
  intro b c
  rw [dist_eq_norm, ← map_sub, freeFlow_norm, dist_eq_norm]

theorem coefficient_freeFlow (t : ℝ) (b : FourierState H) (m : ℤ) :
    coefficient (freeFlow t b) m = phase t m • coefficient b m := by
  simp only [coefficient, freeFlow_apply]
  exact smul_comm _ _ _

variable [CompleteSpace H]

omit [CompleteSpace H] in
theorem freeFlow_eq_tsum (t : ℝ) (b : FourierState H) :
    freeFlow t b = ∑' m : ℤ, lp.single 1 m (phase t m • b m) := by
  have h := lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤) (freeFlow t b)
  simpa only [freeFlow_apply] using h.tsum_eq.symm

theorem freeFlow_continuous (b : FourierState H) :
    Continuous (fun t : ℝ => freeFlow t b) := by
  have hterm (m : ℤ) : Continuous
      (fun t : ℝ => lp.single (E := fun _ : ℤ => H) 1 m (phase t m • b m)) := by
    have hc : Continuous (fun t : ℝ => phase t m • b m) :=
      (phase_continuous m).smul continuous_const
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => H) 1 m).continuous.comp hc
  have hc := continuous_tsum hterm (state_summable_norm b) (fun m t => by
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_smul, phase_norm, one_mul])
  simpa only [← freeFlow_eq_tsum] using hc

theorem freeFlow_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => freeFlow p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, htime⟩ := Metric.continuousAt_iff.mp
    (freeFlow_continuous p.2).continuousAt (ε/2) (by positivity)
  refine ⟨min δ (ε/2), lt_min hδ (by positivity), ?_⟩
  intro q hq
  change max (dist q.1 p.1) (dist q.2 p.2) < min δ (ε/2) at hq
  have ht : dist q.1 p.1 < δ :=
    (lt_of_le_of_lt (le_max_left _ _) hq).trans_le (min_le_left _ _)
  have hb : dist q.2 p.2 < ε/2 :=
    (lt_of_le_of_lt (le_max_right _ _) hq).trans_le (min_le_right _ _)
  have h := htime ht
  calc
    dist (freeFlow q.1 q.2) (freeFlow p.1 p.2) ≤
        dist (freeFlow q.1 q.2) (freeFlow q.1 p.2) +
          dist (freeFlow q.1 p.2) (freeFlow p.1 p.2) := dist_triangle _ _ _
    _ = dist q.2 p.2 + dist (freeFlow q.1 p.2) (freeFlow p.1 p.2) := by
      rw [(freeFlow_isometry q.1).dist_eq]
    _ < ε := by linarith

end NDEAEvolve.Exp014
