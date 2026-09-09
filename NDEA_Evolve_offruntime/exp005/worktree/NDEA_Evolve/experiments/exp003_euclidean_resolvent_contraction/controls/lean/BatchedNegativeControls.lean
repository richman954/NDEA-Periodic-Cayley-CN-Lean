import NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction

/-!
Resource-bounded execution driver for the two frozen false controls.

Each theorem body and target below is reconstructed byte-for-byte from a
hash-pinned rejected fixture, apart from the theorem-name suffix. Keeping both
commands in one Lean process shares the large `Mathlib` import while still
requiring two distinct, attributable type-mismatch diagnostics. This file is
assurance input and is never a production module.
-/

namespace NDEAEvolve.Exp003.NegativeControls

open NDEAEvolve.Exp002
open NDEAEvolve.Exp003.AdversarialWitnesses

/- Deliberately false: the identity resolvent has norm exactly one. -/
theorem false_strict_resolvent_contraction_batched :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 (0 : Mat 1))‖ < 1 := by
  exact zero_generator_not_strict_contraction

/- Deliberately false: the specified non-Hermitian scalar has resolvent norm two. -/
theorem false_resolvent_nonexpansive_without_hermiticity_batched :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 imaginaryHalf)‖ ≤ 1 := by
  exact nonhermitian_resolvent_not_nonexpansive

end NDEAEvolve.Exp003.NegativeControls
