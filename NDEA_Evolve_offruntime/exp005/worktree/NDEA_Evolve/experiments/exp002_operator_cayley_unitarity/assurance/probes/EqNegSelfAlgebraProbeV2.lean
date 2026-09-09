import NDEAEvolve.Experiments.Exp002.OperatorCayley

/-! Minimal algebraic probe for the repaired wrong-sign argument.

This probe imports the same verified Exp002 core as the production witness module,
but does not elaborate the concrete Pauli-matrix witnesses.
-/

theorem eq_zero_of_eq_neg_self_probe_v2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (x : V) (hSign : x = -x) : x = 0 := by
  have hTwice : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = x + (-x) := congrArg (fun y : V => x + y) hSign
      _ = 0 := add_neg_cancel _
  rcases smul_eq_zero.mp hTwice with hTwo | hZero
  · norm_num at hTwo
  · exact hZero
