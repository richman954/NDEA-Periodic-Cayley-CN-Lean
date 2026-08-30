
import Mathlib
import NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1

noncomputable section

open Matrix Complex
open scoped BigOperators

namespace NDEAMathlibGate
namespace PeriodicShift1DV1

/-!
Periodic one-dimensional cyclic shifts over `Fin n`.

This module is deliberately limited to the finite shift layer:

* explicit cyclic next/previous permutations;
* inverse index laws;
* finite-sum invariance under reindexing;
* Euclidean vector shift and inverse shift;
* exact Euclidean and weighted-norm preservation;
* associated complex permutation matrices;
* permutation-matrix unitarity;
* bridge to the existing V9 column-state representation.

No periodic Laplacian, finite-difference consistency, continuous-PDE
convergence, or kernel-only global closure theorem is claimed here.
-/

abbrev VecState (n : Nat) :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.VecState n

abbrev ColumnState (n : Nat) :=
  NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.ColumnState n

abbrev Mat (n : Nat) :=
  Matrix (Fin n) (Fin n) ℂ

/-- Cyclic forward permutation on `Fin n`. -/
def nextPerm (n : Nat) : Equiv.Perm (Fin n) :=
  finRotate n

/-- Inverse cyclic permutation. -/
def prevPerm (n : Nat) : Equiv.Perm (Fin n) :=
  (nextPerm n)⁻¹

/-- Forward periodic index. -/
def nextIdx {n : Nat} (i : Fin n) : Fin n :=
  nextPerm n i

/-- Backward periodic index. -/
def prevIdx {n : Nat} (i : Fin n) : Fin n :=
  prevPerm n i

@[simp]
theorem prevIdx_nextIdx {n : Nat} (i : Fin n) :
    prevIdx (nextIdx i) = i := by
  simpa [prevIdx, nextIdx, prevPerm] using
    (nextPerm n).symm_apply_apply i

@[simp]
theorem nextIdx_prevIdx {n : Nat} (i : Fin n) :
    nextIdx (prevIdx i) = i := by
  simpa [prevIdx, nextIdx, prevPerm] using
    (nextPerm n).apply_symm_apply i

/-- A finite sum is invariant under the forward cyclic reindexing. -/
theorem sum_nextIdx {n : Nat} {M : Type*}
    [AddCommMonoid M]
    (f : Fin n → M) :
    (∑ i : Fin n, f (nextIdx i)) =
      ∑ i : Fin n, f i := by
  simpa [nextIdx] using
    (Equiv.sum_comp (nextPerm n) f)

/-- A finite sum is invariant under the inverse cyclic reindexing. -/
theorem sum_prevIdx {n : Nat} {M : Type*}
    [AddCommMonoid M]
    (f : Fin n → M) :
    (∑ i : Fin n, f (prevIdx i)) =
      ∑ i : Fin n, f i := by
  simpa [prevIdx] using
    (Equiv.sum_comp (prevPerm n) f)

/-- Forward shift on the Euclidean state space. -/
def shiftVec {n : Nat} (psi : VecState n) : VecState n :=
  WithLp.toLp 2
    (fun i => WithLp.ofLp psi (nextIdx i))

/-- Inverse shift on the Euclidean state space. -/
def unshiftVec {n : Nat} (psi : VecState n) : VecState n :=
  WithLp.toLp 2
    (fun i => WithLp.ofLp psi (prevIdx i))

@[simp]
theorem shiftVec_apply {n : Nat}
    (psi : VecState n) (i : Fin n) :
    WithLp.ofLp (shiftVec psi) i =
      WithLp.ofLp psi (nextIdx i) := by
  rfl

@[simp]
theorem unshiftVec_apply {n : Nat}
    (psi : VecState n) (i : Fin n) :
    WithLp.ofLp (unshiftVec psi) i =
      WithLp.ofLp psi (prevIdx i) := by
  rfl

@[simp]
theorem unshiftVec_shiftVec {n : Nat}
    (psi : VecState n) :
    unshiftVec (shiftVec psi) = psi := by
  ext i
  change
    WithLp.ofLp psi (nextIdx (prevIdx i)) =
      WithLp.ofLp psi i
  rw [nextIdx_prevIdx]

@[simp]
theorem shiftVec_unshiftVec {n : Nat}
    (psi : VecState n) :
    shiftVec (unshiftVec psi) = psi := by
  ext i
  change
    WithLp.ofLp psi (prevIdx (nextIdx i)) =
      WithLp.ofLp psi i
  rw [prevIdx_nextIdx]

/-- Complex permutation matrix representing the forward shift. -/
def shiftMatrix (n : Nat) : Mat n :=
  Equiv.Perm.permMatrix ℂ (nextPerm n)

/-- Complex permutation matrix representing the inverse shift. -/
def unshiftMatrix (n : Nat) : Mat n :=
  Equiv.Perm.permMatrix ℂ (prevPerm n)

/-- Permutation-matrix action is composition with the cyclic permutation. -/
theorem shiftMatrix_mulVec {n : Nat}
    (v : Fin n → ℂ) :
    (shiftMatrix n).mulVec v =
      v ∘ nextPerm n := by
  simpa [shiftMatrix] using
    (Matrix.permMatrix_mulVec
      (R := ℂ)
      (nextPerm n)
      (v := v))

@[simp]
theorem shiftMatrix_mulVec_apply {n : Nat}
    (v : Fin n → ℂ) (i : Fin n) :
    (shiftMatrix n).mulVec v i =
      v (nextIdx i) := by
  rw [shiftMatrix_mulVec]
  rfl

/-- The matrix action agrees with the Euclidean forward shift. -/
theorem shiftMatrix_action_eq_shiftVec {n : Nat}
    (psi : VecState n) :
    WithLp.toLp 2
        ((shiftMatrix n).mulVec (WithLp.ofLp psi))
      =
    shiftVec psi := by
  ext i
  change
    (shiftMatrix n).mulVec (WithLp.ofLp psi) i =
      WithLp.ofLp psi (nextIdx i)
  exact shiftMatrix_mulVec_apply (WithLp.ofLp psi) i

/-- The adjoint of the shift matrix is the inverse shift matrix. -/
theorem star_shiftMatrix (n : Nat) :
    star (shiftMatrix n) = unshiftMatrix n :=
by
  change (shiftMatrix n).conjTranspose = unshiftMatrix n
  simp [shiftMatrix, unshiftMatrix, prevPerm]

/-- Right inverse law for the shift matrices. -/
theorem shiftMatrix_mul_unshiftMatrix (n : Nat) :
    shiftMatrix n * unshiftMatrix n = 1 :=
by
  simpa [shiftMatrix, unshiftMatrix, prevPerm] using
    (Matrix.permMatrix_mul
      (R := ℂ)
      (nextPerm n)⁻¹
      (nextPerm n)).symm

/-- Left inverse law for the shift matrices. -/
theorem unshiftMatrix_mul_shiftMatrix (n : Nat) :
    unshiftMatrix n * shiftMatrix n = 1 :=
by
  simpa [shiftMatrix, unshiftMatrix, prevPerm] using
    (Matrix.permMatrix_mul
      (R := ℂ)
      (nextPerm n)
      (nextPerm n)⁻¹).symm

/-- The cyclic shift permutation matrix is unitary. -/
theorem shiftMatrix_isUnitary (n : Nat) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
      (shiftMatrix n) := by
  unfold NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsUnitary
  rw [star_shiftMatrix]
  exact ⟨
    shiftMatrix_mul_unshiftMatrix n,
    unshiftMatrix_mul_shiftMatrix n
  ⟩

/-- The matrix-column action agrees with the V9 column bridge. -/
theorem shiftMatrix_column_action {n : Nat}
    (psi : VecState n) :
    shiftMatrix n *
        NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi
      =
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn
      (shiftVec psi) := by
  calc
    shiftMatrix n *
          NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi
        =
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn
        (WithLp.toLp 2
          ((shiftMatrix n).mulVec (WithLp.ofLp psi))) := by
            exact
              NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.matrix_mul_toColumn
                (shiftMatrix n)
                psi
    _ =
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn
        (shiftVec psi) := by
          rw [shiftMatrix_action_eq_shiftVec]

/-- The forward cyclic shift preserves the Euclidean squared norm. -/
theorem shiftVec_norm_sq {n : Nat}
    (psi : VecState n) :
    ‖shiftVec psi‖ ^ 2 = ‖psi‖ ^ 2 :=
by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change
    (∑ i : Fin n,
      ‖WithLp.ofLp psi (nextIdx i)‖ ^ 2)
      =
    ∑ i : Fin n,
      ‖WithLp.ofLp psi i‖ ^ 2
  exact
    sum_nextIdx
      (fun i : Fin n => ‖WithLp.ofLp psi i‖ ^ 2)

/-- The inverse cyclic shift preserves the Euclidean squared norm. -/
theorem unshiftVec_norm_sq {n : Nat}
    (psi : VecState n) :
    ‖unshiftVec psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  rw [← shiftVec_norm_sq (unshiftVec psi)]
  simp

/-- The cyclic shift preserves the actual Euclidean norm. -/
theorem shiftVec_norm {n : Nat}
    (psi : VecState n) :
    ‖shiftVec psi‖ = ‖psi‖ := by
  have hSqrt :
      Real.sqrt (‖shiftVec psi‖ ^ 2) =
        Real.sqrt (‖psi‖ ^ 2) := by
    rw [shiftVec_norm_sq]
  rwa [
    Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)
  ] at hSqrt

/-- The cyclic shift preserves the weighted discrete squared norm. -/
theorem shiftVec_weightedNormSq {n : Nat}
    (h : ℝ) (psi : VecState n) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
        h (shiftVec psi)
      =
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq
        h psi := by
  exact
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNormSq_preserved
      h
      (shiftVec_norm_sq psi)

/-- The cyclic shift preserves the weighted actual norm. -/
theorem shiftVec_weightedNorm {n : Nat}
    (h : ℝ) (psi : VecState n) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        h (shiftVec psi)
      =
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        h psi := by
  exact
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm_preserved
      h
      (shiftVec_norm_sq psi)

/-- V9's finite column norm is preserved by the cyclic permutation matrix. -/
theorem shiftMatrix_preserves_v9_normSq {n : Nat}
    (psi : VecState n) :
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
      (shiftMatrix n *
        NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi)
      =
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq
      (NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.toColumn psi) := by
  rw [shiftMatrix_column_action]
  rw [
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.v9_normSq_toColumn,
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.v9_normSq_toColumn,
    shiftVec_norm_sq
  ]


def periodicShiftStatusV1 : String :=
  "finite_periodic_shift_validated"

def periodicLaplacianClaimStatusV1 : String :=
  "not_claimed"

def broadContinuousPDEConvergenceClaimStatusV1 : String :=
  "not_claimed"

def kernelOnlyGlobalClosureClaimStatusV1 : String :=
  "not_claimed"

theorem true_periodic_shift_status :
    periodicShiftStatusV1 =
      "finite_periodic_shift_validated" := by
  rfl

theorem true_periodic_laplacian_not_claimed :
    periodicLaplacianClaimStatusV1 =
      "not_claimed" := by
  rfl

theorem true_broad_pde_not_claimed :
    broadContinuousPDEConvergenceClaimStatusV1 =
      "not_claimed" := by
  rfl

theorem true_kernel_only_not_claimed :
    kernelOnlyGlobalClosureClaimStatusV1 =
      "not_claimed" := by
  rfl

#check prevIdx_nextIdx
#check nextIdx_prevIdx
#check sum_nextIdx
#check sum_prevIdx
#check unshiftVec_shiftVec
#check shiftVec_unshiftVec
#check star_shiftMatrix
#check shiftMatrix_isUnitary
#check shiftMatrix_column_action
#check shiftVec_norm_sq
#check shiftVec_weightedNorm
#check shiftMatrix_preserves_v9_normSq

end PeriodicShift1DV1
end NDEAMathlibGate
