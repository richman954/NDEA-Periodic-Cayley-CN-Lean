import Mathlib.Data.Complex.Basic

example : (2 : ℂ) + Complex.I ^ 2 = 1 := by
  rw [Complex.I_sq]
  norm_num
