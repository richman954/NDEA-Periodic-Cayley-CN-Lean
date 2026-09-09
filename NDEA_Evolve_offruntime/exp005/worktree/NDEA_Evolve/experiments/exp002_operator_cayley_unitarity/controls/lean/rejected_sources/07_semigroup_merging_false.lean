import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: two unit steps do not merge into one doubled scalar Cayley step. -/
theorem false_scalar_semigroup_merging :
    scalarCayley 1 * scalarCayley 1 = scalarCayley 2 := by
  exact false_semigroup_merging_witness

end NDEAEvolve.Exp002.NegativeControls
