import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: swapping only the left inverse pair changes the sandwich. -/
theorem false_one_sided_inverse_permutation :
    cayleyR 1 nilB * cayleyR 1 nilA * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA =
      cayleyR 1 nilA * cayleyR 1 nilB * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA := by
  exact cayleyR_one_sided_inverse_permutation_detected

end NDEAEvolve.Exp002.NegativeControls
