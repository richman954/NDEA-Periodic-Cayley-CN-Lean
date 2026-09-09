import FourierReconstruction
import SpatialL2

/-! Exact continuum and discrete Parseval for the actual full odd-grid Fourier
reconstruction. The continuum norm is the accepted interval-integral spatialL2.
No inverse bound or assumption of a band representation replaces this identity. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

private theorem fnorm_phase_continuous (m : ℤ) :
    Continuous (fun x : ℝ => phase ((m : ℝ)*x)) :=
  continuous_iff_continuousAt.mpr fun x => (Exp008.phaseMode_hasDerivAt m x).continuousAt

/-- Every nonzero integer character has zero integral over a full period. -/
theorem phaseMode_integral_zero (m : ℤ) (hm : m ≠ 0) (b : ℝ) :
    (∫ x in b..b+2*Real.pi, phase ((m : ℝ)*x)) = 0 := by
  have hc := ((fnorm_phase_continuous m).mul_const Complex.I).mul_const (m : ℂ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := b) (b := b+2*Real.pi)
    (fun x _ => Exp008.phaseMode_hasDerivAt m x) (hc.intervalIntegrable b (b+2*Real.pi))
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const] at hi
  have hp : phase ((m : ℝ)*(b+2*Real.pi)) = phase ((m : ℝ)*b) :=
    integer_phase_periodic m b
  rw [hp, sub_self, mul_assoc] at hi
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact (mul_eq_zero.mp hi).resolve_right (mul_ne_zero Complex.I_ne_zero hmC)

private theorem fnorm_mode_inner (m l : ℤ) (u v : E 2) (x : ℝ) :
    inner ℂ (phase ((m : ℝ)*x) • u) (phase ((l : ℝ)*x) • v) =
      phase (((l-m : ℤ) : ℝ)*x) * inner ℂ u v := by
  rw [inner_smul_left, inner_smul_right, phase_conj, ← mul_assoc, ← phase_add]
  congr 2
  push_cast
  ring

private theorem fnorm_mode_inner_integral (m l : ℤ) (u v : E 2) (b : ℝ) :
    (∫ x in b..b+2*Real.pi,
      inner ℂ (phase ((m : ℝ)*x) • u) (phase ((l : ℝ)*x) • v)) =
      if m = l then ((2*Real.pi : ℝ) : ℂ) * inner ℂ u v else 0 := by
  simp_rw [fnorm_mode_inner]
  rw [intervalIntegral.integral_mul_const]
  by_cases hml : m = l
  · subst l
    simp [phase_zero, Complex.real_smul]
  · rw [phaseMode_integral_zero (l-m) (sub_ne_zero.mpr (Ne.symm hml)) b, zero_mul, if_neg hml]

/-- Continuum Parseval uses the unnormalized length-2π interval integral. -/
theorem fourierSynthesis_integral_norm_sq (M : ℕ) (a : Fin (2*M+1) → E 2) (b : ℝ) :
    (∫ x in b..b+2*Real.pi, ‖fourierSynthesis M a x‖^2) =
      (2*Real.pi) * ∑ m : Fin (2*M+1), ‖a m‖^2 := by
  classical
  let f := fun (m : Fin (2*M+1)) (x : ℝ) => phase ((oddFrequency M m : ℝ)*x) • a m
  have hc (m : Fin (2*M+1)) : Continuous (f m) :=
    (fnorm_phase_continuous (oddFrequency M m)).smul continuous_const
  have hci (m l : Fin (2*M+1)) : Continuous (fun x => inner ℂ (f m x) (f l x)) :=
    (hc m).inner (hc l)
  have hi : (∫ x in b..b+2*Real.pi,
      inner ℂ (fourierSynthesis M a x) (fourierSynthesis M a x)) =
      ((2*Real.pi : ℝ) : ℂ) * ∑ m : Fin (2*M+1), inner ℂ (a m) (a m) := by
    change (∫ x in b..b+2*Real.pi, inner ℂ (∑ m, f m x) (∑ m, f m x)) = _
    simp only [sum_inner, inner_sum]
    rw [intervalIntegral.integral_finsetSum
      (fun l _ => (continuous_finsetSum _ (fun m _ => hci m l)).intervalIntegrable b (b+2*Real.pi))]
    have hsum (l : Fin (2*M+1)) :
        (∫ x in b..b+2*Real.pi, ∑ m : Fin (2*M+1), inner ℂ (f m x) (f l x)) =
        ∑ m : Fin (2*M+1), ∫ x in b..b+2*Real.pi, inner ℂ (f m x) (f l x) :=
      intervalIntegral.integral_finsetSum
        (fun m _ => (hci m l).intervalIntegrable b (b+2*Real.pi))
    simp_rw [hsum]
    dsimp only [f]
    simp_rw [fnorm_mode_inner_integral]
    have he (m l : Fin (2*M+1)) : oddFrequency M m = oddFrequency M l ↔ m = l :=
      (oddFrequency_injective M).eq_iff
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
  have hnorm (u : E 2) : inner ℂ u u = ((‖u‖^2 : ℝ) : ℂ) := by
    calc
      _ = (‖u‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K u
      _ = _ := by simp only [Complex.ofReal_pow]
  simp_rw [hnorm] at hi
  rw [intervalIntegral.integral_ofReal] at hi
  exact_mod_cast hi

theorem fourierSynthesis_spatialL2 (M : ℕ) (a : Fin (2*M+1) → E 2) (b : ℝ) :
    Exp015.spatialL2 (fourierSynthesis M a) b (2*Real.pi) =
      Real.sqrt (2*Real.pi) * Real.sqrt (∑ m : Fin (2*M+1), ‖a m‖^2) := by
  unfold Exp015.spatialL2
  rw [fourierSynthesis_integral_norm_sq, Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]

private theorem fnorm_sum_norm_sq {ι H : Type*} [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset ι) (f : ι → H) (horth : ∀ i j, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖^2 = ∑ i ∈ s, ‖f i‖^2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have his : inner ℂ (f i) (∑ j ∈ s, f j) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (by intro he; exact hi (he.symm ▸ hj))
    have hpy : ‖f i + ∑ j ∈ s, f j‖^2 = ‖f i‖^2 + ‖∑ j ∈ s, f j‖^2 := by
      simpa only [← pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ his
    rw [Finset.sum_insert hi, hpy, ih, Finset.sum_insert hi]

private theorem fnorm_frequency_bound (M : ℕ) (m : Fin (2*M+1)) :
    |(oddFrequency M m : ℝ)| ≤ (M : ℝ) := by
  have hm : m.val ≤ 2*M := Nat.le_of_lt_succ m.isLt
  have hmR : (m.val : ℝ) ≤ 2*(M : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m.val := Nat.cast_nonneg _
  simp only [oddFrequency, Int.cast_sub, Int.cast_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Discrete Parseval for the same centered Fin-indexed synthesis and existing sampler. -/
theorem fourierSynthesis_sample_norm_sq (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi) (a : Fin (2*M+1) → E 2) :
    ‖Exp010.sampleSolution (2*M) h (fun _ => fourierSynthesis M a) 0‖^2 =
      ((2*M+1 : ℕ) : ℝ) * ∑ m : Fin (2*M+1), ‖a m‖^2 := by
  classical
  have he : Exp010.sampleSolution (2*M) h (fun _ => fourierSynthesis M a) 0 =
      ∑ m : Fin (2*M+1), modeLiftCLM (2*M) h (oddFrequency M m) (a m) := by
    ext p
    simp [Exp010.sampleSolution, fourierSynthesis, modeLiftCLM, modeLiftLinear, modeLift]
  rw [he]
  have ho (m l : Fin (2*M+1)) (hml : m ≠ l) :
      inner ℂ (modeLiftCLM (2*M) h (oddFrequency M m) (a m))
        (modeLiftCLM (2*M) h (oddFrequency M l) (a l)) = 0 := by
    apply modeLift_inner_eq_zero (2*M) h hmesh
    exact band_difference_not_dvd M (2*M) (oddFrequency M m) (oddFrequency M l)
      (fnorm_frequency_bound M m) (fnorm_frequency_bound M l) (by omega)
      (fun he => hml (oddFrequency_injective M he))
  rw [fnorm_sum_norm_sq Finset.univ _ ho]
  simp only [modeLiftCLM_apply, modeLift_norm_sq, Finset.mul_sum]

/-- Coefficients of every grid state satisfy Parseval, using proved sampling fidelity. -/
theorem fourierCoefficient_norm_sq (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi) (y : Vec (Grid (2*M))) :
    ‖y‖^2 = ((2*M+1 : ℕ) : ℝ) * ∑ m : Fin (2*M+1), ‖fourierCoefficient M h y m‖^2 := by
  have hn := fourierSynthesis_sample_norm_sq M h hmesh (fourierCoefficient M h y)
  change ‖Exp010.sampleSolution (2*M) h (fun _ => fourierReconstruction M h y) 0‖^2 = _ at hn
  rw [sampleSolution_fourierReconstruction M h hmesh y] at hn
  exact hn

/-- The faithful continuum L2 isometry for the actual arbitrary-grid reconstruction. -/
theorem fourierReconstruction_spatialL2 (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi) (y : Vec (Grid (2*M))) (b : ℝ) :
    Exp015.spatialL2 (fourierReconstruction M h y) b (2*Real.pi) = Real.sqrt h * ‖y‖ := by
  have hN : (0 : ℝ) < ((2*M+1 : ℕ) : ℝ) := by positivity
  have hh : 0 ≤ h := by nlinarith [Real.pi_pos]
  apply (sq_eq_sq₀ (Exp015.spatialL2_nonneg _ _ _) (by positivity)).mp
  rw [Exp015.spatialL2_sq _ b (2*Real.pi) (by positivity), mul_pow,
    Real.sq_sqrt hh, fourierCoefficient_norm_sq M h hmesh y]
  change (∫ x in b..b+2*Real.pi,
    ‖fourierSynthesis M (fourierCoefficient M h y) x‖^2) = _
  rw [fourierSynthesis_integral_norm_sq]
  rw [← mul_assoc, mul_comm h, hmesh]

#print axioms phaseMode_integral_zero
#print axioms fourierSynthesis_integral_norm_sq
#print axioms fourierSynthesis_spatialL2
#print axioms fourierSynthesis_sample_norm_sq
#print axioms fourierCoefficient_norm_sq
#print axioms fourierReconstruction_spatialL2
end NDEAEvolve.Exp016
