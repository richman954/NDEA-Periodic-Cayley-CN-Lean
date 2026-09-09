import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

/-!
Resource-bounded execution driver for the seven existing false controls.

Each theorem body and target below is the corresponding rejected fixture's
mathematical content.  Keeping all seven commands in one Lean process shares the
large `Mathlib` import while still requiring Lean to emit seven distinct errors.
This file is assurance input, never a production module.
-/

namespace NDEAEvolve.Exp002.NegativeControls

open AdversarialWitnesses

/-- False: the shear generator shows that Hermiticity cannot simply be dropped. -/
theorem false_dropped_hermiticity_batched :
    IsUnitary (cayley 1 shearA) := by
  exact nonhermitian_cayley_not_unitary

/-- False: allowing a non-real step destroys the scalar unit-modulus identity. -/
theorem false_complex_step_unitarity_batched :
    star (complexStepCayley (Complex.I / 2)) *
        complexStepCayley (Complex.I / 2) = 1 := by
  exact complex_step_half_not_unitary

/-- False: the actual Pauli Cayley transforms do not become order independent. -/
theorem false_order_independence_batched :
    cayley 1 pauliX * cayley 1 pauliZ = cayley 1 pauliZ * cayley 1 pauliX := by
  exact pauli_cayley_factors_order_sensitive

/-- False: reversing the sign of the Pauli commutator changes a nonzero defect. -/
theorem false_wrong_defect_sign_batched :
    commutator (cayley 1 pauliX) (cayley 1 pauliZ) =
      -commutator (cayley 1 pauliX) (cayley 1 pauliZ) := by
  exact pauli_cayley_commutator_wrong_sign

/-- False: swapping only the left inverse pair changes the sandwich. -/
theorem false_one_sided_inverse_permutation_batched :
    cayleyR 1 nilB * cayleyR 1 nilA * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA =
      cayleyR 1 nilA * cayleyR 1 nilB * commutator nilA nilB *
        cayleyR 1 nilB * cayleyR 1 nilA := by
  exact cayleyR_one_sided_inverse_permutation_detected

/-- False: omitting the nonzero-step hypothesis makes the commutation equivalence fail. -/
theorem false_zero_step_commutation_equivalence_batched :
    Commute (cayley 0 pauliX) (cayley 1 pauliZ) ↔ Commute pauliX pauliZ := by
  exact zero_step_breaks_commutation_iff

/-- False: two unit steps do not merge into one doubled scalar Cayley step. -/
theorem false_scalar_semigroup_merging_batched :
    scalarCayley 1 * scalarCayley 1 = scalarCayley 2 := by
  exact false_semigroup_merging_witness

end NDEAEvolve.Exp002.NegativeControls
