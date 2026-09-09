import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Global evolution for a uniformly bounded, time-dependent linear ODE.
The Dyson series is constructed by actual iterated interval integrals. Its
factorial bound and locally uniform derivative bounds justify differentiation
at every real time, including negative time. -/

noncomputable section
open scoped Topology BigOperators NNReal
open Set MeasureTheory intervalIntegral

namespace NDEAEvolve.Exp014

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def dysonTerm (A : ℝ → E →L[ℝ] E) (x₀ : E) : ℕ → ℝ → E
  | 0, _ => x₀
  | n + 1, t => ∫ s in 0..t, A s (dysonTerm A x₀ n s)

theorem dysonTerm_continuous (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2)) (x₀ : E) (n : ℕ) :
    Continuous (dysonTerm A x₀ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n hn =>
    have hc : Continuous (fun t => A t (dysonTerm A x₀ n t)) :=
      hA.comp (continuous_id.prodMk hn)
    exact continuous_primitive (fun a b => hc.intervalIntegrable a b) 0

theorem dysonTerm_succ_hasDerivAt (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2)) (x₀ : E) (n : ℕ) (t : ℝ) :
    HasDerivAt (dysonTerm A x₀ (n + 1)) (A t (dysonTerm A x₀ n t)) t := by
  have hc : Continuous (fun s => A s (dysonTerm A x₀ n s)) :=
    hA.comp (continuous_id.prodMk (dysonTerm_continuous A hA x₀ n))
  exact integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt

theorem dysonTerm_succ_zero (A : ℝ → E →L[ℝ] E) (x₀ : E) (n : ℕ) :
    dysonTerm A x₀ (n + 1) 0 = 0 := by
  simp [dysonTerm]

theorem dysonTerm_norm_le (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (n : ℕ) (t : ℝ) :
    ‖dysonTerm A x₀ n t‖ ≤ (K * |t|) ^ n / n.factorial * ‖x₀‖ := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n hn =>
    change ‖∫ s in 0..t, A s (dysonTerm A x₀ n s)‖ ≤ _
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t,
          (K : ℝ) ^ (n + 1) * |s - 0| ^ n / n.factorial * ‖x₀‖ := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        calc
          ‖A s (dysonTerm A x₀ n s)‖ ≤ K * ‖dysonTerm A x₀ n s‖ :=
            (A s).le_of_opNorm_le (hK s) _
          _ ≤ K * ((K * |s|) ^ n / n.factorial * ‖x₀‖) := by
            gcongr
            exact hn s
          _ = (K : ℝ) ^ (n + 1) * |s - 0| ^ n / n.factorial * ‖x₀‖ := by
            rw [sub_zero, mul_pow, pow_succ]
            ring
      _ ≤ (K * |t|) ^ (n + 1) / (n + 1).factorial * ‖x₀‖ := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_norm, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow,
          sub_zero]

theorem dysonTerm_summable (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    Summable (fun n => dysonTerm A x₀ n t) := by
  exact ((Real.summable_pow_div_factorial (K * |t|)).mul_right ‖x₀‖).of_norm_bounded
    (fun n => dysonTerm_norm_le A K hK x₀ n t)

def linearEvolution (A : ℝ → E →L[ℝ] E) (x₀ : E) (t : ℝ) : E :=
  ∑' n, dysonTerm A x₀ n t

theorem linearEvolution_eq_head_add (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    linearEvolution A x₀ t = x₀ + ∑' n, dysonTerm A x₀ (n + 1) t := by
  exact (dysonTerm_summable A K hK x₀ t).tsum_eq_zero_add

theorem linearEvolution_zero (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) :
    linearEvolution A x₀ 0 = x₀ := by
  rw [linearEvolution_eq_head_add A K hK]
  simp only [dysonTerm_succ_zero, tsum_zero, add_zero]

theorem linearEvolution_hasDerivAt (A : ℝ → E →L[ℝ] E)
    (hA : Continuous (fun p : ℝ × E => A p.1 p.2))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) (t : ℝ) :
    HasDerivAt (linearEvolution A x₀) (A t (linearEvolution A x₀ t)) t := by
  let R : ℝ := |t| + 1
  let bound : ℕ → ℝ := fun n => K * ((K * R) ^ n / n.factorial * ‖x₀‖)
  have hb : Summable bound :=
    ((Real.summable_pow_div_factorial (K * R)).mul_right ‖x₀‖).mul_left (K : ℝ)
  have hg : ∀ n s, s ∈ Ioo (-R) R →
      ‖A s (dysonTerm A x₀ n s)‖ ≤ bound n := by
    intro n s hs
    calc
      _ ≤ K * ‖dysonTerm A x₀ n s‖ := (A s).le_of_opNorm_le (hK s) _
      _ ≤ K * ((K * |s|) ^ n / n.factorial * ‖x₀‖) := by
        gcongr
        exact dysonTerm_norm_le A K hK x₀ n s
      _ ≤ bound n := by
        dsimp [bound]
        gcongr
        exact (abs_lt.mpr hs).le
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := by dsimp [R]; constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-R) R := by
    rw [← abs_lt]
    exact lt_add_one |t|
  have hsum0 : Summable (fun n => dysonTerm A x₀ (n + 1) 0) := by
    simpa only [dysonTerm_succ_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : E)))
  have hd := hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n s _ => dysonTerm_succ_hasDerivAt A hA x₀ n s) hg hzero hsum0 ht
  have hmap : (∑' n, A t (dysonTerm A x₀ n t)) = A t (linearEvolution A x₀ t) :=
    ((A t).map_tsum (dysonTerm_summable A K hK x₀ t)).symm
  rw [hmap] at hd
  have hder := (hasDerivAt_const t x₀).add hd
  simp only [zero_add] at hder
  convert hder using 1
  ext s
  exact linearEvolution_eq_head_add A K hK x₀ s

theorem operatorEvaluation_continuous (A : ℝ → E →L[ℝ] E)
    (hA : ∀ x, Continuous (fun t => A t x))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) :
    Continuous (fun p : ℝ × E => A p.1 p.2) := by
  exact continuous_prod_of_continuous_lipschitzWith' _ K
    (fun t => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t)) hA

theorem exists_global_linear_solution (A : ℝ → E →L[ℝ] E)
    (hA : ∀ x, Continuous (fun t => A t x))
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ ∀ t, HasDerivAt u (A t (u t)) t := by
  exact ⟨linearEvolution A x₀, linearEvolution_zero A K hK x₀,
    linearEvolution_hasDerivAt A (operatorEvaluation_continuous A hA K hK) K hK x₀⟩

end NDEAEvolve.Exp014
