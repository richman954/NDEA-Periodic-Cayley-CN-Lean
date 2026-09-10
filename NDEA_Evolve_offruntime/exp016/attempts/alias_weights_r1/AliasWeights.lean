import GridAlias
import WeightedFourier

/-! Centered sampling aliases and weighted absolute DFT sums.
These use the actual odd-grid coefficients and Exp014's squared weight.
The exponent p = 2 is the fourth frequency weight needed for stencil control.
No regularity or moment hypothesis is imposed on an infinite potential here.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

theorem oddFrequency_abs_le (M : ℕ) (r : Fin (2 * M + 1)) :
    |(oddFrequency M r : ℝ)| ≤ (M : ℝ) := by
  have hr : r.val ≤ 2 * M := Nat.le_of_lt_succ r.isLt
  have hrR : (r.val : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
  simp only [oddFrequency, Int.cast_sub, Int.cast_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The unique centered alias has minimum absolute frequency. -/
theorem gridAlias_abs_le (M : ℕ) (ell : ℤ) (r : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r) :
    |(oddFrequency M r : ℝ)| ≤ |(ell : ℝ)| := by
  by_cases he : |(ell : ℝ)| ≤ (M : ℝ)
  · have heZ : |ell| ≤ (M : ℤ) := by exact_mod_cast he
    have hb := abs_le.mp heZ
    have hj0 : 0 ≤ ell + (M : ℤ) := by omega
    let s : Fin (2 * M + 1) := ⟨(ell + (M : ℤ)).toNat, by omega⟩
    have hf : oddFrequency M s = ell := by
      change ((ell + (M : ℤ)).toNat : ℤ) - (M : ℤ) = ell
      rw [Int.toNat_of_nonneg hj0]
      omega
    have hs : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M s := by
      rw [hf, sub_self]
      exact dvd_zero _
    have hrs : r = s := (existsUnique_gridAlias M ell).unique hr hs
    rw [hrs, hf]
  · exact (oddFrequency_abs_le M r).trans (le_of_lt (lt_of_not_ge he))

/-- Powers of the sealed Exp014 weight; p = 2 means (1+|m|)^4. -/
def frequencyWeight (p : ℕ) (m : ℤ) : ℝ := Exp014.weight m ^ p

theorem frequencyWeight_nonneg (p : ℕ) (m : ℤ) : 0 ≤ frequencyWeight p m :=
  pow_nonneg (Exp014.weight_pos m).le p

theorem frequencyWeight_two (m : ℤ) :
    frequencyWeight 2 m = (1 + |(m : ℝ)|) ^ 4 := by
  simp only [frequencyWeight, Exp014.weight, ← pow_mul]

theorem frequencyWeight_add_le (p : ℕ) (m n : ℤ) :
    frequencyWeight p (m + n) ≤ frequencyWeight p m * frequencyWeight p n := by
  unfold frequencyWeight
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Exp014.weight_pos _).le (Exp014.weight_add_le m n) p

theorem gridAlias_frequencyWeight_le (p M : ℕ) (ell : ℤ) (r : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r) :
    frequencyWeight p (oddFrequency M r) ≤ frequencyWeight p ell := by
  have hw : Exp014.weight (oddFrequency M r) ≤ Exp014.weight ell := by
    unfold Exp014.weight
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add_left (gridAlias_abs_le M ell r hr) 1) 2
  exact pow_le_pow_left₀ (Exp014.weight_pos _).le hw p

/-- Folding a product frequency preserves submultiplicativity, without N factors. -/
theorem gridAlias_frequencyWeight_add_le (p M : ℕ) (ell m : ℤ)
    (r : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell + m - oddFrequency M r) :
    frequencyWeight p (oddFrequency M r) ≤ frequencyWeight p ell * frequencyWeight p m :=
  (gridAlias_frequencyWeight_le p M (ell + m) r hr).trans
    (frequencyWeight_add_le p ell m)

/-- Absolute weighted sum of the actual normalized full-grid DFT coefficients. -/
def fourierWeightedNorm (p M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) : ℝ :=
  ∑ r : Fin (2 * M + 1), frequencyWeight p (oddFrequency M r) *
    ‖fourierCoefficient M h y r‖

theorem fourierWeightedNorm_nonneg (p M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) :
    0 ≤ fourierWeightedNorm p M h y :=
  Finset.sum_nonneg fun r _ => mul_nonneg (frequencyWeight_nonneg p _) (norm_nonneg _)

theorem fourierWeightedNorm_sum_le (p M : ℕ) (h : ℝ) {ι : Type*}
    (s : Finset ι) (y : ι → Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (∑ i ∈ s, y i) ≤ ∑ i ∈ s, fourierWeightedNorm p M h (y i) := by
  simp only [fourierWeightedNorm, ← fourierCoefficientCLM_apply, map_sum]
  calc
    _ ≤ ∑ r : Fin (2 * M + 1), frequencyWeight p (oddFrequency M r) *
        ∑ i ∈ s, ‖fourierCoefficientCLM M h r (y i)‖ := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (frequencyWeight_nonneg p _)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

/-- A single sampled mode has exactly the weight of its centered representative. -/
theorem fourierWeightedNorm_modeLift_eq (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (r : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r) (u : E 2) :
    fourierWeightedNorm p M h (modeLiftCLM (2 * M) h ell u) =
      frequencyWeight p (oddFrequency M r) * ‖u‖ := by
  classical
  have hc (s : Fin (2 * M + 1)) :
      ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M s ↔ s = r :=
    ⟨fun hs => (existsUnique_gridAlias M ell).unique hs hr, fun he => he.symm ▸ hr⟩
  simp only [fourierWeightedNorm, fourierCoefficient_modeLift_alias M h hmesh, hc]
  simp

/-- Immediate DFT consumer of alias minimization, valid also for unresolved modes. -/
theorem fourierWeightedNorm_modeLift_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (ell : ℤ) (u : E 2) :
    fourierWeightedNorm p M h (modeLiftCLM (2 * M) h ell u) ≤
      frequencyWeight p ell * ‖u‖ := by
  obtain ⟨r, hr, _⟩ := existsUnique_gridAlias M ell
  rw [fourierWeightedNorm_modeLift_eq p M h hmesh ell r hr]
  exact mul_le_mul_of_nonneg_right (gridAlias_frequencyWeight_le p M ell r hr) (norm_nonneg u)

#print axioms oddFrequency_abs_le
#print axioms gridAlias_abs_le
#print axioms frequencyWeight_nonneg
#print axioms frequencyWeight_two
#print axioms frequencyWeight_add_le
#print axioms gridAlias_frequencyWeight_le
#print axioms gridAlias_frequencyWeight_add_le
#print axioms fourierWeightedNorm_nonneg
#print axioms fourierWeightedNorm_sum_le
#print axioms fourierWeightedNorm_modeLift_eq
#print axioms fourierWeightedNorm_modeLift_le
end NDEAEvolve.Exp016
