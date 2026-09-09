import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: omitting the nonzero-step hypothesis makes the commutation equivalence fail. -/
theorem false_zero_step_commutation_equivalence :
    Commute (cayley 0 pauliX) (cayley 1 pauliZ) ↔ Commute pauliX pauliZ := by
  exact zero_step_breaks_commutation_iff

end NDEAEvolve.Exp002.NegativeControls
