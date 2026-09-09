import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: allowing a non-real step destroys the scalar unit-modulus identity. -/
theorem false_complex_step_unitarity :
    star (complexStepCayley (Complex.I / 2)) *
        complexStepCayley (Complex.I / 2) = 1 := by
  exact complex_step_half_not_unitary

end NDEAEvolve.Exp002.NegativeControls
