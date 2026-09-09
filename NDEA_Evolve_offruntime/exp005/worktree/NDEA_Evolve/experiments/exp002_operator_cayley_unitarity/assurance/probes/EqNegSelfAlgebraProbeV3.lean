import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Minimal algebraic probe for the repaired wrong-sign argument.

Unlike the second probe, this imports only the algebraic typeclasses needed by
the helper and therefore does not pay the cost of loading the Exp002 matrix core.
-/

theorem eq_zero_of_eq_neg_self_probe_v3 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (x : V) (hSign : x = -x) : x = 0 := by
  have hTwice : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = x + (-x) := congrArg (fun y : V => x + y) hSign
      _ = 0 := add_neg_cancel _
  rcases smul_eq_zero.mp hTwice with hTwo | hZero
  · norm_num at hTwo
  · exact hZero
