import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

/-!
Isolated probe for the repaired proof term in
`AdversarialWitnesses.pauli_cayley_commutator_wrong_sign`.

This imports the last green positive-witness `.olean`, whose unchanged Pauli
definitions and order-sensitivity theorem are the only witness declarations
used below. The statement and repaired proof body match the pending production
helper. A later full module build is still required.
-/

noncomputable section

open Matrix

namespace NDEAEvolve
namespace Exp002
namespace AssuranceProbes

open AdversarialWitnesses

theorem pauli_cayley_commutator_wrong_sign_probe :
    commutator (cayley 1 pauliX) (cayley 1 pauliZ) ≠
      -commutator (cayley 1 pauliX) (cayley 1 pauliZ) := by
  intro hSign
  have hTwice :
      (2 : ℂ) • commutator (cayley 1 pauliX) (cayley 1 pauliZ) = 0 := by
    rw [two_smul]
    calc
      commutator (cayley 1 pauliX) (cayley 1 pauliZ) +
          commutator (cayley 1 pauliX) (cayley 1 pauliZ) =
        commutator (cayley 1 pauliX) (cayley 1 pauliZ) +
          (-commutator (cayley 1 pauliX) (cayley 1 pauliZ)) :=
            congrArg
              (fun K : Mat2 =>
                commutator (cayley 1 pauliX) (cayley 1 pauliZ) + K)
              hSign
      _ = 0 := add_neg_cancel _
  have hZero : commutator (cayley 1 pauliX) (cayley 1 pauliZ) = 0 := by
    rcases smul_eq_zero.mp hTwice with hTwo | hZero
    · norm_num at hTwo
    · exact hZero
  have hCommute : Commute (cayley 1 pauliX) (cayley 1 pauliZ) :=
    (commutator_eq_zero_iff_commute _ _).mp hZero
  exact pauli_cayley_factors_order_sensitive hCommute.eq

end AssuranceProbes
end Exp002
end NDEAEvolve
