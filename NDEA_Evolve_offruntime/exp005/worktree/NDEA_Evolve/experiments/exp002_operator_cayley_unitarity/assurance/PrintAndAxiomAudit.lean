/-
Copyright (c) 2026 NDEA-Evolve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NDEA-Evolve
-/
import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

/-!
# Experiment 002 declaration and axiom audit

This non-production audit unit prints the exact headline declarations and their
transitive axiom dependencies.
-/

set_option pp.proofs false

#check @NDEAEvolve.Exp002.cayleyD_isUnit
#check @NDEAEvolve.Exp002.cayleyD_det_ne_zero
#check @NDEAEvolve.Exp002.cayley_unitary
#check @NDEAEvolve.Exp002.cayley_preserves_inner
#check @NDEAEvolve.Exp002.cayley_preserves_norm
#check @NDEAEvolve.Exp002.orderedCayleyProduct_unitary
#check @NDEAEvolve.Exp002.orderedCayleyProduct_preserves_inner
#check @NDEAEvolve.Exp002.orderedCayleyProduct_preserves_norm
#check @NDEAEvolve.Exp002.cayley_order_defect
#check @NDEAEvolve.Exp002.cayley_commute_iff_of_inverse_laws
#check @NDEAEvolve.Exp002.hermitian_cayley_commute_iff
#check @NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_factors_order_sensitive
#check @NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_commutator_wrong_sign
#check @NDEAEvolve.Exp002.AdversarialWitnesses.nonhermitian_cayley_not_unitary
#check @NDEAEvolve.Exp002.AdversarialWitnesses.complex_step_half_not_unitary
#check @NDEAEvolve.Exp002.AdversarialWitnesses.zero_step_breaks_commutation_iff
#check @NDEAEvolve.Exp002.AdversarialWitnesses.cayleyR_one_sided_inverse_permutation_detected

#print NDEAEvolve.Exp002.cayleyD_isUnit
#print NDEAEvolve.Exp002.cayleyD_det_ne_zero
#print NDEAEvolve.Exp002.cayley_unitary
#print NDEAEvolve.Exp002.cayley_preserves_inner
#print NDEAEvolve.Exp002.cayley_preserves_norm
#print NDEAEvolve.Exp002.orderedCayleyProduct_unitary
#print NDEAEvolve.Exp002.orderedCayleyProduct_preserves_inner
#print NDEAEvolve.Exp002.orderedCayleyProduct_preserves_norm
#print NDEAEvolve.Exp002.cayley_order_defect
#print NDEAEvolve.Exp002.cayley_commute_iff_of_inverse_laws
#print NDEAEvolve.Exp002.hermitian_cayley_commute_iff
#print NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_factors_order_sensitive
#print NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_commutator_wrong_sign
#print NDEAEvolve.Exp002.AdversarialWitnesses.nonhermitian_cayley_not_unitary
#print NDEAEvolve.Exp002.AdversarialWitnesses.complex_step_half_not_unitary
#print NDEAEvolve.Exp002.AdversarialWitnesses.zero_step_breaks_commutation_iff
#print NDEAEvolve.Exp002.AdversarialWitnesses.cayleyR_one_sided_inverse_permutation_detected

#print axioms NDEAEvolve.Exp002.cayleyD_isUnit
#print axioms NDEAEvolve.Exp002.cayleyD_det_ne_zero
#print axioms NDEAEvolve.Exp002.cayley_unitary
#print axioms NDEAEvolve.Exp002.cayley_preserves_inner
#print axioms NDEAEvolve.Exp002.cayley_preserves_norm
#print axioms NDEAEvolve.Exp002.orderedCayleyProduct_unitary
#print axioms NDEAEvolve.Exp002.orderedCayleyProduct_preserves_inner
#print axioms NDEAEvolve.Exp002.orderedCayleyProduct_preserves_norm
#print axioms NDEAEvolve.Exp002.cayley_order_defect
#print axioms NDEAEvolve.Exp002.cayley_commute_iff_of_inverse_laws
#print axioms NDEAEvolve.Exp002.hermitian_cayley_commute_iff
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_factors_order_sensitive
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_commutator_wrong_sign
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.nonhermitian_cayley_not_unitary
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.complex_step_half_not_unitary
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.zero_step_breaks_commutation_iff
#print axioms NDEAEvolve.Exp002.AdversarialWitnesses.cayleyR_one_sided_inverse_permutation_detected
