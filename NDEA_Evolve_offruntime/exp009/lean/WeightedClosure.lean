import InfiniteClosure
import WeightedTail

/-! Quantitative full-reference error under a weighted coefficient moment. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp009

theorem weighted_infinite_grid_error_bound (r M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n))
    (ha : Summable fun m => frequencyWeight r m * ‖a m‖)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    infiniteGridError n h k N a initial ≤ infiniteInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a +
        2*(moment r a / ((M:ℝ)+1)^r)) := by
  apply (infinite_grid_error_bound M n h k T N a initial
    (weighted_summable_implies_absolute r a ha) hM hband hmesh hh hMh hk hstep horizon).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (tail_le_moment_div r M a ha)
      (by norm_num : (0:ℝ)≤2))) (Real.sqrt_nonneg _))

end NDEAEvolve.Exp009
