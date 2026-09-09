import Continuity
import Mathlib.Analysis.Calculus.MeanValue

/-! Global time and space bounds for the actual classical Fourier solution.
The second weighted coefficient moment bounds the actual derivatives, and
the mean value inequality converts those bounds to pointwise differences. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

theorem derivative_space_norm_le (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    ‖deriv (infiniteSolution a t) x‖ ≤ moment 2 a := by
  rw [infiniteSolution_space_derivative a ha t x]
  exact (norm_tsum_le_tsum_norm (regular_space_summable_norm a ha t x)).trans
    ((regular_space_summable_norm a ha t x).tsum_le_tsum
      (fun m => modeSpace_norm_le m (a m) t x) ha)

theorem derivative_time_norm_le (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    ‖deriv (fun s => infiniteSolution a s x) t‖ ≤ 2 * moment 2 a := by
  rw [infiniteSolution_time_derivative a ha t x]
  calc
    _ ≤ ∑' m, ‖modeTime m (a m) t x‖ :=
      norm_tsum_le_tsum_norm (regular_time_summable_norm a ha t x)
    _ ≤ ∑' m, 2 * frequencyWeight 2 m * ‖a m‖ :=
      (regular_time_summable_norm a ha t x).tsum_le_tsum
        (fun m => modeTime_norm_le m (a m) t x) (regular_time_majorant a ha)
    _ = 2 * moment 2 a := by simp only [mul_assoc, tsum_mul_left, moment]

theorem solution_space_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t x y : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a t y‖ ≤ moment 2 a * |x - y| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun z _ => (infiniteSolution_space_hasDerivAt a ha t z).differentiableAt)
    (fun z _ => derivative_space_norm_le a ha t z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hb

theorem solution_time_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t s x : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s x‖ ≤ 2 * moment 2 a * |t - s| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun z _ => (infiniteSolution_time_hasDerivAt a ha z x).differentiableAt)
    (fun z _ => derivative_time_norm_le a ha z x) convex_univ
    (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hb

theorem solution_space_lipschitz (a : ℤ → E 2) (ha : Regular a) (t x y : ℝ) :
    ‖infiniteSolution a t y - infiniteSolution a t x‖ ≤ moment 2 a * |y - x| :=
  solution_space_norm_sub_le a ha t y x

theorem solution_time_lipschitz (a : ℤ → E 2) (ha : Regular a) (x s t : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s x‖ ≤ 2 * moment 2 a * |t - s| :=
  solution_time_norm_sub_le a ha t s x

theorem solution_norm_sub_le (a : ℤ → E 2) (ha : Regular a) (t s x y : ℝ) :
    ‖infiniteSolution a t x - infiniteSolution a s y‖ ≤
      2 * moment 2 a * |t - s| + moment 2 a * |x - y| := by
  calc
    _ ≤ ‖infiniteSolution a t x - infiniteSolution a s x‖ +
        ‖infiniteSolution a s x - infiniteSolution a s y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (solution_time_norm_sub_le a ha t s x)
      (solution_space_norm_sub_le a ha s x y)

end NDEAEvolve.Exp011
