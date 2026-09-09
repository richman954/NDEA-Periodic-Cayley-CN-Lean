import NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction

open NDEAEvolve.Exp002
open NDEAEvolve.Exp003.AdversarialWitnesses

/- Deliberately false: the specified non-Hermitian scalar has resolvent norm two. -/
theorem false_resolvent_nonexpansive_without_hermiticity :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 imaginaryHalf)‖ ≤ 1 := by
  exact nonhermitian_resolvent_not_nonexpansive
