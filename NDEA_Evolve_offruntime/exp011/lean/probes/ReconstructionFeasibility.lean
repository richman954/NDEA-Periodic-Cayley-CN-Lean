import ClassicalClosure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011.Probe

def nodeValue (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) : E 2 :=
  WithLp.toLp 2 (fun b => v (j,b))

theorem nodeValue_norm_le (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) :
    ‖nodeValue n v j‖ ≤ ‖v‖ := by
  have hs : ‖nodeValue n v j‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [nodeValue, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [norm_nonneg (nodeValue n v j), norm_nonneg v]

def spaceIndex (n : ℕ) (h x : ℝ) : Fin (n+1) :=
  ⟨min ⌊x/h⌋₊ n, lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self n)⟩

theorem spaceIndex_distance (n : ℕ) (h x : ℝ) (hh : 0<h)
    (hx : 0≤x) (hL : x≤((n+1:ℕ):ℝ)*h) :
    0≤x-(spaceIndex n h x).val*h ∧ x-(spaceIndex n h x).val*h≤h := by
  have hfloor := Nat.floor_le (div_nonneg hx hh.le)
  have hleft : ((min ⌊x/h⌋₊ n : ℕ):ℝ)≤x/h :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans hfloor
  have hleft' := (le_div_iff₀ hh).mp hleft
  constructor
  · change 0≤x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h
    linarith
  · change x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h≤h
    by_cases hf : ⌊x/h⌋₊≤n
    · rw [min_eq_left hf]
      have hr := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x/h))
      nlinarith
    · rw [min_eq_right (le_of_not_ge hf)]
      push_cast at hL
      nlinarith

theorem derivative_space_norm_le (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    ‖deriv (infiniteSolution a t) x‖ ≤ moment 2 a := by
  rw [infiniteSolution_space_derivative a ha t x]
  exact (norm_tsum_le_tsum_norm (regular_space_summable_norm a ha t x)).trans
    ((regular_space_summable_norm a ha t x).tsum_le_tsum
      (fun m => modeSpace_norm_le m (a m) t x) ha)

theorem solution_space_lipschitz (a : ℤ → E 2) (ha : Regular a) (t x y : ℝ) :
    ‖infiniteSolution a t y-infiniteSolution a t x‖ ≤ moment 2 a*|y-x| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (fun z _ => (infiniteSolution_space_hasDerivAt a ha t z).differentiableAt)
    (fun z _ => derivative_space_norm_le a ha t z) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs] using hb

end NDEAEvolve.Exp011.Probe
