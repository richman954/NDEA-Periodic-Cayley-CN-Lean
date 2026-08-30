import NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Complex Set
open scoped Interval

namespace NDEAMathlibGate.TemporalTaylorRemainderBoundsV1

def quadraticTaylor (f : ℝ → ℂ) (t k : ℝ) : ℂ :=
  f t + k • iteratedDeriv 1 f t +
    (k ^ 2 / 2) • iteratedDeriv 2 f t

def linearTaylor (f : ℝ → ℂ) (t k : ℝ) : ℂ :=
  f t + k • iteratedDeriv 1 f t

def quadraticWithin (f : ℝ → ℂ) (s : Set ℝ) (t k : ℝ) : ℂ :=
  f t + k • iteratedDerivWithin 1 f s t +
    (k ^ 2 / 2) • iteratedDerivWithin 2 f s t

def linearWithin (f : ℝ → ℂ) (s : Set ℝ) (t k : ℝ) : ℂ :=
  f t + k • iteratedDerivWithin 1 f s t

theorem taylor_degree2_within
    (f : ℝ → ℂ) (s : Set ℝ) (t k : ℝ) :
    taylorWithinEval f 2 s t (t + k) = quadraticWithin f s t k := by
  simp [taylor_within_apply, quadraticWithin]
  left
  ring

theorem taylor_degree1_within
    (f : ℝ → ℂ) (s : Set ℝ) (t k : ℝ) :
    taylorWithinEval f 1 s t (t + k) = linearWithin f s t k := by
  simp [taylor_within_apply, linearWithin]

theorem taylorWithinEval_two_eq
    (f : ℝ → ℂ) (t k : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 3 f) :
    taylorWithinEval f 2 (Set.Icc t (t + k)) t (t + k) =
      quadraticTaylor f t k := by
  have hu : UniqueDiffOn ℝ (Set.Icc t (t + k)) :=
    uniqueDiffOn_Icc (by linarith)
  have ht : t ∈ Set.Icc t (t + k) := ⟨le_rfl, by linarith⟩
  have h1 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 1) (f := f) (s := Set.Icc t (t + k)) (x := t)
    hu (hf.contDiffAt.of_le (by norm_num)) ht
  have h2 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 2) (f := f) (s := Set.Icc t (t + k)) (x := t)
    hu (hf.contDiffAt.of_le (by norm_num)) ht
  rw [taylor_degree2_within]
  simp only [quadraticWithin, quadraticTaylor, h1, h2]

theorem taylorWithinEval_one_eq
    (f : ℝ → ℂ) (t k : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 2 f) :
    taylorWithinEval f 1 (Set.Icc t (t + k)) t (t + k) =
      linearTaylor f t k := by
  have hu : UniqueDiffOn ℝ (Set.Icc t (t + k)) :=
    uniqueDiffOn_Icc (by linarith)
  have ht : t ∈ Set.Icc t (t + k) := ⟨le_rfl, by linarith⟩
  have h1 := iteratedDerivWithin_eq_iteratedDeriv
    (n := 1) (f := f) (s := Set.Icc t (t + k)) (x := t)
    hu (hf.contDiffAt.of_le (by norm_num)) ht
  rw [taylor_degree1_within]
  simp only [linearWithin, linearTaylor, h1]

def quadraticRemainder (f : ℝ → ℂ) (t k : ℝ) : ℂ :=
  f (t + k) - quadraticTaylor f t k

def linearRemainder (f : ℝ → ℂ) (t k : ℝ) : ℂ :=
  f (t + k) - linearTaylor f t k

def quadraticRemainderIntegrand (f : ℝ → ℂ) (t k x : ℝ) : ℂ :=
  ((t + k - x) ^ 2 / (Nat.factorial 2 : ℝ)) •
    iteratedDerivWithin 3 f (Set.Icc t (t + k)) x

def linearRemainderIntegrand (f : ℝ → ℂ) (t k x : ℝ) : ℂ :=
  (t + k - x) • iteratedDerivWithin 2 f (Set.Icc t (t + k)) x

theorem quadraticRemainder_integral
    (f : ℝ → ℂ) (t k : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 3 f) :
    quadraticRemainder f t k =
      ∫ x in t..t + k, quadraticRemainderIntegrand f t k x := by
  rw [quadraticRemainder, ← taylorWithinEval_two_eq f t k hk hf]
  simpa [quadraticRemainderIntegrand, Set.uIcc_of_le (by linarith : t ≤ t + k)] using
    (taylor_integral_remainder
      (f := f) (x := t + k) (x₀ := t) (n := 2) hf.contDiffOn)

theorem linearRemainder_integral
    (f : ℝ → ℂ) (t k : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 2 f) :
    linearRemainder f t k =
      ∫ x in t..t + k, linearRemainderIntegrand f t k x := by
  rw [linearRemainder, ← taylorWithinEval_one_eq f t k hk hf]
  simpa [linearRemainderIntegrand, Set.uIcc_of_le (by linarith : t ≤ t + k)] using
    (taylor_integral_remainder
      (f := f) (x := t + k) (x₀ := t) (n := 1) hf.contDiffOn)

theorem quadraticRemainder_norm_bound
    (f : ℝ → ℂ) (t k M : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 3 f)
    (hderiv : ∀ x ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 3 f (Set.Icc t (t + k)) x‖ ≤ M) :
    ‖quadraticRemainder f t k‖ ≤ M * k ^ 3 / 6 := by
  have hM : 0 ≤ M :=
    (norm_nonneg _).trans
      (hderiv (t + k) (Set.right_mem_Icc.2 (by linarith)))
  have hae : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.uIoc t (t + k)),
      ‖quadraticRemainderIntegrand f t k x‖ ≤
        (M / 2) * |x - (t + k)| ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun x hx ↦ by
      have hxI : x ∈ Set.Icc t (t + k) := by
        have hx' : x ∈ Set.Ioc t (t + k) := by
          simpa [Set.uIoc_of_le (by linarith : t ≤ t + k)] using hx
        exact ⟨hx'.1.le, hx'.2⟩
      have hd := hderiv x hxI
      have hcoeff :
          |(t + k - x) ^ 2 / (Nat.factorial 2 : ℝ)| =
            |x - (t + k)| ^ 2 / 2 := by
        rw [abs_div, abs_pow, abs_sub_comm]
        norm_num
      rw [quadraticRemainderIntegrand, norm_smul, Real.norm_eq_abs, hcoeff]
      calc
        |x - (t + k)| ^ 2 / 2 *
            ‖iteratedDerivWithin 3 f (Icc t (t + k)) x‖ ≤
            (|x - (t + k)| ^ 2 / 2) * M :=
          mul_le_mul_of_nonneg_left hd (by positivity)
        _ = (M / 2) * |x - (t + k)| ^ 2 := by ring
  have hg : IntervalIntegrable
      (fun x : ℝ ↦ (M / 2) * |x - (t + k)| ^ 2)
      MeasureTheory.volume t (t + k) :=
    (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.pow 2)).intervalIntegrable _ _
  rw [quadraticRemainder_integral f t k hk hf]
  calc
    ‖∫ x in t..t + k, quadraticRemainderIntegrand f t k x‖ ≤
        |∫ x in t..t + k, (M / 2) * |x - (t + k)| ^ 2| :=
      intervalIntegral.norm_integral_le_abs_of_norm_le hae hg
    _ = M * k ^ 3 / 6 := by
      rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + k)]
      rw [← Set.uIoc_of_le (by linarith : t ≤ t + k), Set.uIoc_comm]
      rw [MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
      rw [show |t - (t + k)| = k by rw [abs_of_neg (by linarith)]; ring]
      rw [abs_of_nonneg (mul_nonneg (div_nonneg hM (by norm_num)) (by positivity))]
      ring

theorem linearRemainder_norm_bound
    (f : ℝ → ℂ) (t k M : ℝ) (hk : 0 < k) (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ x ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 2 f (Set.Icc t (t + k)) x‖ ≤ M) :
    ‖linearRemainder f t k‖ ≤ M * k ^ 2 / 2 := by
  have hM : 0 ≤ M :=
    (norm_nonneg _).trans
      (hderiv (t + k) (Set.right_mem_Icc.2 (by linarith)))
  have hae : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.uIoc t (t + k)),
      ‖linearRemainderIntegrand f t k x‖ ≤ M * |x - (t + k)| ^ 1 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun x hx ↦ by
      have hxI : x ∈ Set.Icc t (t + k) := by
        have hx' : x ∈ Set.Ioc t (t + k) := by
          simpa [Set.uIoc_of_le (by linarith : t ≤ t + k)] using hx
        exact ⟨hx'.1.le, hx'.2⟩
      have hd := hderiv x hxI
      rw [linearRemainderIntegrand, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      calc
        |x - (t + k)| * ‖iteratedDerivWithin 2 f (Icc t (t + k)) x‖ ≤
            |x - (t + k)| * M :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = M * |x - (t + k)| ^ 1 := by ring
  have hg : IntervalIntegrable
      (fun x : ℝ ↦ M * |x - (t + k)| ^ 1)
      MeasureTheory.volume t (t + k) :=
    (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.pow 1)).intervalIntegrable _ _
  rw [linearRemainder_integral f t k hk hf]
  calc
    ‖∫ x in t..t + k, linearRemainderIntegrand f t k x‖ ≤
        |(∫ x in t..t + k, M * |x - (t + k)| ^ 1)| :=
      intervalIntegral.norm_integral_le_abs_of_norm_le hae hg
    _ = M * k ^ 2 / 2 := by
      rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + k)]
      rw [← Set.uIoc_of_le (by linarith : t ≤ t + k), Set.uIoc_comm]
      rw [MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
      rw [show |t - (t + k)| = k by rw [abs_of_neg (by linarith)]; ring]
      rw [abs_of_nonneg (mul_nonneg hM (by positivity))]
      ring

#check taylorWithinEval_two_eq
#check taylorWithinEval_one_eq
#check quadraticRemainder_norm_bound
#check linearRemainder_norm_bound

end NDEAMathlibGate.TemporalTaylorRemainderBoundsV1
