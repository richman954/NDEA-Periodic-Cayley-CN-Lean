import InfiniteReference

/-! A weighted absolutely summable coefficient moment gives a quantitative
Fourier tail estimate. The exponent is a natural number. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp009

def frequencyWeight (r : ℕ) (m : ℤ) : ℝ := (1 + |(m : ℝ)|)^r
def moment (r : ℕ) (a : ℤ → E 2) : ℝ :=
  ∑' m, frequencyWeight r m * ‖a m‖

theorem frequencyWeight_one_le (r : ℕ) (m : ℤ) : 1 ≤ frequencyWeight r m := by
  exact one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])

theorem frequencyWeight_nonneg (r : ℕ) (m : ℤ) : 0 ≤ frequencyWeight r m :=
  le_trans (by norm_num) (frequencyWeight_one_le r m)

theorem moment_nonneg (r : ℕ) (a : ℤ → E 2) : 0 ≤ moment r a :=
  tsum_nonneg fun m => mul_nonneg (frequencyWeight_nonneg r m) (norm_nonneg _)

theorem weighted_summable_implies_absolute (r : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    Summable fun m => ‖a m‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ha
  intro m
  exact le_mul_of_one_le_left (norm_nonneg _) (frequencyWeight_one_le r m)

theorem mass_le_moment (r : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    mass a ≤ moment r a := by
  apply (weighted_summable_implies_absolute r a ha).tsum_le_tsum _ ha
  intro m
  exact le_mul_of_one_le_left (norm_nonneg _) (frequencyWeight_one_le r m)

theorem outside_band_weight (r M : ℕ) (m : ℤ) (hm : m ∉ band M) :
    ((M : ℝ)+1)^r ≤ frequencyWeight r m := by
  have hab : (M : ℤ) < |m| := by
    by_contra hn
    have hp := abs_le.mp (le_of_not_gt hn)
    exact hm (Finset.mem_Icc.mpr hp)
  have habr : (M : ℝ) < |(m : ℝ)| := by exact_mod_cast hab
  unfold frequencyWeight
  apply pow_le_pow_left₀ (by positivity)
  linarith

theorem weighted_tail_bound (r M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    ((M : ℝ)+1)^r * tail M a ≤ moment r a := by
  have habs := weighted_summable_implies_absolute r a ha
  rw [tail_eq_tsum_compl M a habs, ← tsum_mul_left]
  have hfirst :
      (∑' m : {m : ℤ // m ∉ band M}, ((M : ℝ)+1)^r*‖a m‖) ≤
      ∑' m : {m : ℤ // m ∉ band M}, frequencyWeight r m * ‖a m‖ := by
    apply ((habs.subtype _).mul_left _).tsum_le_tsum _ (ha.subtype _)
    intro m
    exact mul_le_mul_of_nonneg_right (outside_band_weight r M m m.property) (norm_nonneg _)
  apply hfirst.trans
  have hparts := ha.sum_add_tsum_subtype_compl (band M)
  have hsum : 0 ≤ ∑ m ∈ band M, frequencyWeight r m * ‖a m‖ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (frequencyWeight_nonneg r m) (norm_nonneg _)
  unfold moment
  linarith

theorem tail_le_moment_div (r M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖) :
    tail M a ≤ moment r a / ((M : ℝ)+1)^r := by
  apply (le_div_iff₀ (by positivity : 0 < ((M : ℝ)+1)^r)).mpr
  simpa only [mul_comm] using weighted_tail_bound r M a ha

end NDEAEvolve.Exp009
