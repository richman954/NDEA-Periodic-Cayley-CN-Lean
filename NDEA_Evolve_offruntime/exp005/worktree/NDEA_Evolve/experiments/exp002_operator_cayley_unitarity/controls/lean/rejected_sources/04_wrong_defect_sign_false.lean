import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: reversing the sign of the Pauli commutator changes a nonzero defect. -/
theorem false_wrong_defect_sign :
    commutator (cayley 1 pauliX) (cayley 1 pauliZ) =
      -commutator (cayley 1 pauliX) (cayley 1 pauliZ) := by
  exact pauli_cayley_commutator_wrong_sign

end NDEAEvolve.Exp002.NegativeControls
