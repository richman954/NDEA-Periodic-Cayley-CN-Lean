import Mathlib
import NDEAMathlibGate.PeriodicShift1DV1
import NDEAMathlibGate.PeriodicLaplacian1DV1

noncomputable section

open Matrix Complex
open scoped BigOperators ComplexOrder

namespace NDEAMathlibGate
namespace PeriodicLaplacian1DV1R

/-!
Append-only repair of the periodic one-dimensional negative Laplacian.

The predecessor `PeriodicLaplacian1DV1` is imported only to preserve and expose
its diagnostic status. No theorem in this module depends on predecessor
mathematics.

Definitions:

  D_h = (1/h) (S-I)
  L_h = D_h* D_h
-/

abbrev VecState (n : Nat) :=
  NDEAMathlibGate.PeriodicShift1DV1.VecState n

abbrev Mat (n : Nat) :=
  Matrix (Fin n) (Fin n) ℂ

/-- The failed V1 predecessor remains diagnostic only. -/
theorem predecessor_not_validated :
    NDEAMathlibGate.PeriodicLaplacian1DV1.periodicLaplacianStatusV1 =
      "not_validated" := by
  exact NDEAMathlibGate.PeriodicLaplacian1DV1.true_diagnostic_status

/-- Complex reciprocal of a real grid spacing. -/
def invSpacing (h : ℝ) : ℂ :=
  (h : ℂ)⁻¹

/-- Forward periodic difference D_h = (1/h)(S-I). -/
def forwardDiffMatrix (h : ℝ) (n : Nat) : Mat n :=
  invSpacing h • (NDEAMathlibGate.PeriodicShift1DV1.shiftMatrix n - 1)

/-- Periodic negative Laplacian L_h = D_h* D_h. -/
def periodicNegLaplacian (h : ℝ) (n : Nat) : Mat n :=
  star (forwardDiffMatrix h n) * forwardDiffMatrix h n

/-- L_h is self-adjoint directly from its Gram factorization. -/
theorem periodicNegLaplacian_star_eq
    (h : ℝ) (n : Nat) :
    star (periodicNegLaplacian h n) =
      periodicNegLaplacian h n := by
  simp [periodicNegLaplacian]

/-- Mathlib Hermiticity statement. -/
theorem periodicNegLaplacian_isHermitian
    (h : ℝ) (n : Nat) :
    (periodicNegLaplacian h n).IsHermitian := by
  exact periodicNegLaplacian_star_eq h n

/-- V9-wrapper Hermiticity statement. -/
theorem periodicNegLaplacian_wrapperHermitian
    (h : ℝ) (n : Nat) :
    NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.IsHermitian
      (periodicNegLaplacian h n) := by
  exact periodicNegLaplacian_star_eq h n

/-- L_h is positive semidefinite as a conjugate-transpose Gram matrix. -/
theorem periodicNegLaplacian_posSemidef
    (h : ℝ) (n : Nat) :
    (periodicNegLaplacian h n).PosSemidef := by
  change
    (star (forwardDiffMatrix h n) *
      forwardDiffMatrix h n).PosSemidef
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.posSemidef_conjTranspose_mul_self
      (forwardDiffMatrix h n))

/-- Explicit bridge between matrix star and conjugate transpose for S. -/
theorem shiftMatrix_conjTranspose (n : Nat) :
    (NDEAMathlibGate.PeriodicShift1DV1.shiftMatrix n).conjTranspose =
      NDEAMathlibGate.PeriodicShift1DV1.unshiftMatrix n := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (NDEAMathlibGate.PeriodicShift1DV1.star_shiftMatrix n)

@[simp]
theorem star_invSpacing (h : ℝ) :
    star (invSpacing h) = invSpacing h := by
  simp [invSpacing]

/-- Explicit adjoint formula for D_h, using matrix star directly. -/
theorem star_forwardDiffMatrix
    (h : ℝ) (n : Nat) :
    star (forwardDiffMatrix h n) =
      invSpacing h • (NDEAMathlibGate.PeriodicShift1DV1.unshiftMatrix n - 1) := by
  simp [
    forwardDiffMatrix,
    invSpacing,
    NDEAMathlibGate.PeriodicShift1DV1.star_shiftMatrix
  ]


/-- Inverse-shift matrix action. -/
theorem unshiftMatrix_mulVec {n : Nat}
    (v : Fin n → ℂ) :
    (NDEAMathlibGate.PeriodicShift1DV1.unshiftMatrix n).mulVec v =
      v ∘ NDEAMathlibGate.PeriodicShift1DV1.prevPerm n := by
  simpa [NDEAMathlibGate.PeriodicShift1DV1.unshiftMatrix] using
    (Matrix.permMatrix_mulVec
      (R := ℂ)
      (NDEAMathlibGate.PeriodicShift1DV1.prevPerm n)
      (v := v))

@[simp]
theorem unshiftMatrix_mulVec_apply {n : Nat}
    (v : Fin n → ℂ)
    (i : Fin n) :
    (NDEAMathlibGate.PeriodicShift1DV1.unshiftMatrix n).mulVec v i =
      v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i) := by
  rw [unshiftMatrix_mulVec]
  rfl

/-- One periodic edge difference. -/
def edgeDifference {n : Nat}
    (v : Fin n → ℂ)
    (i : Fin n) : ℂ :=
  v (NDEAMathlibGate.PeriodicShift1DV1.nextIdx i) - v i

/-- D_h action on one component. -/
@[simp]
theorem forwardDiffMatrix_mulVec_apply
    {n : Nat}
    (h : ℝ)
    (v : Fin n → ℂ)
    (i : Fin n) :
    (forwardDiffMatrix h n).mulVec v i =
      invSpacing h * edgeDifference v i := by
  simp [
    forwardDiffMatrix,
    edgeDifference,
    Matrix.smul_mulVec,
    Matrix.sub_mulVec,
    NDEAMathlibGate.PeriodicShift1DV1.shiftMatrix_mulVec_apply
  ]

/-- D_h* action on one component. -/
@[simp]
theorem star_forwardDiffMatrix_mulVec_apply
    {n : Nat}
    (h : ℝ)
    (v : Fin n → ℂ)
    (i : Fin n) :
    (star (forwardDiffMatrix h n)).mulVec v i =
      invSpacing h *
        (v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i) - v i) := by
  rw [star_forwardDiffMatrix]
  simp [
    Matrix.smul_mulVec,
    Matrix.sub_mulVec,
    unshiftMatrix_mulVec_apply
  ]

/-- Reciprocal squared is the reciprocal of the square. -/
theorem invSpacing_sq (h : ℝ) :
    invSpacing h ^ 2 =
      ((h : ℂ) ^ 2)⁻¹ := by
  simp [invSpacing, inv_pow]

/-- Reciprocal-square normalization. -/
theorem invSpacing_sq_mul
    (h : ℝ)
    (z : ℂ) :
    invSpacing h ^ 2 * z =
      z / (h : ℂ) ^ 2 := by
  rw [invSpacing_sq]
  simp [div_eq_mul_inv, mul_comm]


/-- Scaled periodic three-point stencil. -/
theorem periodicNegLaplacian_mulVec_apply_scaled
    {n : Nat}
    (h : ℝ)
    (v : Fin n → ℂ)
    (i : Fin n) :
    (periodicNegLaplacian h n).mulVec v i =
      invSpacing h ^ 2 *
        (2 * v i -
          v (NDEAMathlibGate.PeriodicShift1DV1.nextIdx i) -
          v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i)) := by
  rw [periodicNegLaplacian]
  rw [← Matrix.mulVec_mulVec]
  rw [star_forwardDiffMatrix_mulVec_apply]
  rw [
    forwardDiffMatrix_mulVec_apply,
    forwardDiffMatrix_mulVec_apply
  ]
  simp [edgeDifference, NDEAMathlibGate.PeriodicShift1DV1.nextIdx_prevIdx]
  ring

/-- Algebraic three-point stencil; division is total in ℂ. -/
theorem periodicNegLaplacian_mulVec_apply_total
    {n : Nat}
    (h : ℝ)
    (v : Fin n → ℂ)
    (i : Fin n) :
    (periodicNegLaplacian h n).mulVec v i =
      (2 * v i -
        v (NDEAMathlibGate.PeriodicShift1DV1.nextIdx i) -
        v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i)) /
      (h : ℂ) ^ 2 := by
  rw [periodicNegLaplacian_mulVec_apply_scaled]
  exact
    invSpacing_sq_mul h
      (2 * v i -
        v (NDEAMathlibGate.PeriodicShift1DV1.nextIdx i) -
        v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i))

/-- Standard physical stencil statement for nonzero spacing. -/
theorem periodicNegLaplacian_mulVec_apply
    {n : Nat}
    (h : ℝ)
    (_hh : h ≠ 0)
    (v : Fin n → ℂ)
    (i : Fin n) :
    (periodicNegLaplacian h n).mulVec v i =
      (2 * v i -
        v (NDEAMathlibGate.PeriodicShift1DV1.nextIdx i) -
        v (NDEAMathlibGate.PeriodicShift1DV1.prevIdx i)) /
      (h : ℂ) ^ 2 := by
  exact periodicNegLaplacian_mulVec_apply_total h v i

/-- Constant vectors are killed by D_h. -/
theorem forwardDiffMatrix_constant_kernel
    {n : Nat}
    (h : ℝ)
    (c : ℂ) :
    (forwardDiffMatrix h n).mulVec
        (fun _ : Fin n => c)
      =
    0 := by
  funext i
  simp [forwardDiffMatrix_mulVec_apply, edgeDifference]

/-- Constant vectors lie in the kernel of L_h. -/
theorem periodicNegLaplacian_constant_kernel
    {n : Nat}
    (h : ℝ)
    (c : ℂ) :
    (periodicNegLaplacian h n).mulVec
        (fun _ : Fin n => c)
      =
    0 := by
  rw [periodicNegLaplacian]
  rw [← Matrix.mulVec_mulVec]
  rw [forwardDiffMatrix_constant_kernel]
  simp

/-- Abstract Gram energy identity. -/
theorem gram_energy_identity
    {n : Nat}
    (h : ℝ)
    (v : Fin n → ℂ) :
    star v ⬝ᵥ
        (periodicNegLaplacian h n).mulVec v
      =
    star ((forwardDiffMatrix h n).mulVec v) ⬝ᵥ
      ((forwardDiffMatrix h n).mulVec v) :=
by
  rw [periodicNegLaplacian]
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.star_eq_conjTranspose]
  rw [← Matrix.star_mulVec]


/-- Weighted finite inner product. -/
def weightedInner
    {n : Nat}
    (h : ℝ)
    (u v : Fin n → ℂ) : ℂ :=
  (h : ℂ) * (star u ⬝ᵥ v)

/-- Weighted abstract Gram identity. -/
theorem weighted_gram_identity
    {n : Nat}
    (h : ℝ)
    (_hh : 0 < h)
    (v : Fin n → ℂ) :
    weightedInner h v
        ((periodicNegLaplacian h n).mulVec v)
      =
    weightedInner h
      ((forwardDiffMatrix h n).mulVec v)
      ((forwardDiffMatrix h n).mulVec v) := by
  unfold weightedInner
  rw [gram_energy_identity]

def periodicLaplacianStatusV1R : String :=
  "periodic_laplacian_gram_stage_validated"

def stencilStatusV1R : String :=
  "three_point_periodic_stencil_validated"

def gramEnergyStatusV1R : String :=
  "abstract_gram_energy_validated"

def summationByPartsStatusV1R : String :=
  "not_validated_in_this_stage"

def constantKernelStatusV1R : String :=
  "constant_state_kernel_validated"

def consistencyOrderClaimStatusV1R : String :=
  "not_claimed"

def semiDiscreteSchrodingerConvergenceClaimStatusV1R : String :=
  "not_claimed"

def broadContinuousPDEConvergenceClaimStatusV1R : String :=
  "not_claimed"

def pmlOperatorStabilityClaimStatusV1R : String :=
  "not_claimed"

def infiniteDimensionalEvolutionClaimStatusV1R : String :=
  "not_claimed"

def generalGaugeStabilityClaimStatusV1R : String :=
  "not_claimed"

def kernelOnlyGlobalClosureClaimStatusV1R : String :=
  "not_claimed"

theorem true_periodic_laplacian_status :
    periodicLaplacianStatusV1R = "periodic_laplacian_gram_stage_validated" := by
  rfl

theorem true_stencil_status :
    stencilStatusV1R = "three_point_periodic_stencil_validated" := by
  rfl

theorem true_gram_status :
    gramEnergyStatusV1R = "abstract_gram_energy_validated" := by
  rfl

theorem true_summation_by_parts_status :
    summationByPartsStatusV1R = "not_validated_in_this_stage" := by
  rfl

theorem true_constant_kernel_status :
    constantKernelStatusV1R = "constant_state_kernel_validated" := by
  rfl

#check periodicNegLaplacian_isHermitian
#check periodicNegLaplacian_posSemidef
#check shiftMatrix_conjTranspose
#check star_forwardDiffMatrix
#check forwardDiffMatrix_mulVec_apply
#check periodicNegLaplacian_mulVec_apply
#check periodicNegLaplacian_constant_kernel
#check gram_energy_identity
#check weighted_gram_identity

end PeriodicLaplacian1DV1R
end NDEAMathlibGate
