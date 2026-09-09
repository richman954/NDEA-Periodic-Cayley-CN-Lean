import NDEAEvolve.Experiments.Exp003.EuclideanResolventContraction

open NDEAEvolve.Exp002
open NDEAEvolve.Exp003.AdversarialWitnesses

/- Deliberately false: the identity resolvent has norm exactly one. -/
theorem false_strict_resolvent_contraction :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 1)
      (cayleyR 1 (0 : Mat 1))‖ < 1 := by
  exact zero_generator_not_strict_contraction
