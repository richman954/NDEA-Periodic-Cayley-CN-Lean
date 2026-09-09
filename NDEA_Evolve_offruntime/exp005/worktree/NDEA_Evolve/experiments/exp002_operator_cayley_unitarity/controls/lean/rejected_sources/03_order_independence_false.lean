import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: the actual Pauli Cayley transforms do not become order independent. -/
theorem false_order_independence :
    cayley 1 pauliX * cayley 1 pauliZ = cayley 1 pauliZ * cayley 1 pauliX := by
  exact pauli_cayley_factors_order_sensitive

end NDEAEvolve.Exp002.NegativeControls
