import Mathlib.Data.Complex.Basic

example : ((1 + Complex.I * (Complex.I / 2)) * 2 : ℂ) = 1 := by
  rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]
  norm_num
