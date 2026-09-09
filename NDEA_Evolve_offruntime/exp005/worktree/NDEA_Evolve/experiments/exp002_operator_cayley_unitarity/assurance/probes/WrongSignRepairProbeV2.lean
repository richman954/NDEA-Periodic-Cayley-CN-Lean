import NDEAEvolve.Experiments.Exp002.OperatorCayley

/-!
Self-contained isolated check for the pending wrong-sign helper. This imports
only the already-green universal core and reconstructs the minimal exact Pauli
premises, so it does not require an `AdversarialWitnesses.olean`.
-/

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace NDEAEvolve
namespace Exp002
namespace AssuranceProbesV2

abbrev Mat2 := Mat 2

def pauliX : Mat2 := !![0, 1; 1, 0]
def pauliZ : Mat2 := !![1, 0; 0, -1]

theorem pauliX_hermitian : pauliX.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply]

theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose_apply]

theorem pauli_generators_do_not_commute : ¬ Commute pauliX pauliZ := by
  intro h
  have h01 := congrFun (congrFun h.eq (0 : Fin 2)) (1 : Fin 2)
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem pauli_cayley_factors_order_sensitive :
    cayley 1 pauliX * cayley 1 pauliZ ≠ cayley 1 pauliZ * cayley 1 pauliX := by
  intro h
  have hFactors : Commute (cayley 1 pauliX) (cayley 1 pauliZ) := h
  have hGenerators : Commute pauliX pauliZ :=
    (hermitian_cayley_commute_iff 1 1 pauliX pauliZ
      pauliX_hermitian pauliZ_hermitian (by norm_num)).mp hFactors
  exact pauli_generators_do_not_commute hGenerators

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

end AssuranceProbesV2
end Exp002
end NDEAEvolve
