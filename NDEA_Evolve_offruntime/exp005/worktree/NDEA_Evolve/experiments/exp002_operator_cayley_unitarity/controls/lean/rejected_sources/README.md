# Experiment 002 Lean rejection fixtures

These seven files are deliberately false, isolated compilation units. Each imports
`NDEAEvolve.Experiments.Exp002.AdversarialWitnesses` and attempts to prove a false
claim by supplying the already-verified theorem proving its negation. A correct Lean
run must return a nonzero exit code and a type-mismatch diagnostic for every file.

| Fixture | False claim | Verified witness supplied | Intended rejection |
|---|---|---|---|
| `01_dropped_hermiticity_false.lean` | Every displayed shear Cayley update is unitary even without Hermiticity. | `nonhermitian_cayley_not_unitary` | The supplied term proves `¬ IsUnitary (cayley 1 shearA)`, not `IsUnitary (cayley 1 shearA)`. |
| `02_complex_step_false.lean` | The scalar Cayley expression remains unitary for step `I / 2`. | `complex_step_half_not_unitary` | The supplied term proves the claimed star-product equality is false. |
| `03_order_independence_false.lean` | The actual Pauli Cayley transforms commute. | `pauli_cayley_factors_order_sensitive` | The supplied term proves the two ordered products are unequal. |
| `04_wrong_defect_sign_false.lean` | The commutator of the actual Pauli Cayley factors equals its negation. | `pauli_cayley_commutator_wrong_sign` | The supplied term derives nonzero order defect from the actual Cayley definitions and proves the sign-reversed equality is false. |
| `05_one_sided_inverse_permutation_false.lean` | A one-sided swap of the actual Cayley inverse factors preserves the order-defect sandwich. | `cayleyR_one_sided_inverse_permutation_detected` | The supplied term connects the explicit inverses and generator commutator to `cayleyR`/`commutator`, then proves the altered and correct sandwiches are unequal. |
| `06_zero_step_iff_false.lean` | Cayley-factor commutation is equivalent to generator commutation even when one step is zero. | `zero_step_breaks_commutation_iff` | The supplied term proves the equivalence is false for the Pauli witnesses. |
| `07_semigroup_merging_false.lean` | Two unit scalar Cayley steps equal one doubled step. | `false_semigroup_merging_witness` | The supplied term proves the proposed semigroup equality is false. |

Execution policy: preserve these seven original fixtures and their frozen hashes.
For the final resource-bounded run, `../BatchedNegativeControls.lean` reconstructs
their targets and proof bodies byte for byte (renaming only each theorem identifier)
and compiles all seven in one Lean process, so the expensive positive-witness import
is shared.  Preserve the one raw process log and seven independently attributable
diagnostic blocks; report seven unique cases and one process invocation.  Acceptance
requires natural exit code 1, exactly seven mapped type mismatches, and no timeout,
truncation, import, syntax, missing, extra, or mixed-witness diagnostic.  Pair this
rejection run with the successful positive-witness module build. These fixtures are
assurance inputs, not production sources.
