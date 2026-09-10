import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace NDEAEvolve.Exp016.Probe
theorem mean_normalization (X Y : ℝ) (h : X ≤ Y) :
    (1 / 2 : ℝ) * X ≤ Y / 2 := by
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using
    mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
#print axioms mean_normalization
end NDEAEvolve.Exp016.Probe
