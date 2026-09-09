import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: the shear generator shows that Hermiticity cannot simply be dropped. -/
theorem false_dropped_hermiticity :
    IsUnitary (cayley 1 shearA) := by
  exact nonhermitian_cayley_not_unitary

end NDEAEvolve.Exp002.NegativeControls
