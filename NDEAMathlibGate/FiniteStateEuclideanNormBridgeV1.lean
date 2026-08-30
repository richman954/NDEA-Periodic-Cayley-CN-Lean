import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import NDEAMathlibGate.GlobalFiniteStackV9_20260712_065344_840597

noncomputable section

namespace NDEAMathlibGate
namespace FiniteStateEuclideanNormBridgeV1

open Matrix Complex
open scoped BigOperators

variable {n : ℕ}

abbrev VecState (n : ℕ) := EuclideanSpace ℂ (Fin n)

abbrev ColumnState (n : ℕ) := 
  NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.State n

def toColumn (ψ : VecState n) : ColumnState n :=
  fun i _ => WithLp.ofLp ψ i

def fromColumn (ψ : ColumnState n) : VecState n :=
  WithLp.toLp 2 (fun i => ψ i 0)

@[simp]
theorem fromColumn_toColumn (ψ : VecState n) :
    fromColumn (toColumn ψ) = ψ := by
  ext i
  rfl

@[simp]
theorem toColumn_fromColumn (ψ : ColumnState n) :
    toColumn (fromColumn ψ) = ψ := by
  ext i j
  fin_cases j
  rfl

@[simp]
theorem matrix_mul_toColumn (A : Matrix (Fin n) (Fin n) ℂ) (ψ : VecState n) :
    A * toColumn ψ = toColumn (WithLp.toLp 2 (A *ᵥ WithLp.ofLp ψ)) := by
  ext i j
  fin_cases j
  simp [toColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct]

@[simp]
theorem fromColumn_matrix_mul (A : Matrix (Fin n) (Fin n) ℂ) (ψ : ColumnState n) :
    fromColumn (A * ψ) = WithLp.toLp 2 (A *ᵥ (fun i => ψ i 0)) := by
  ext i
  simp [fromColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Bridge V9's custom normSq to Mathlib's Euclidean L2 norm squared. -/
theorem v9_normSq_toColumn (ψ : VecState n) :
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq (toColumn ψ) = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV2_Iterated.normSq,
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.normSq,
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.normSqC,
    NDEAMathlibGate.CayleyTimeStepperFiniteStabilityV1R3.adjointState,
    Matrix.mul_apply,
    dotProduct,
    toColumn,
    Complex.conj_mul'
  ]
  -- Resolve the final scalar equality over the finite sum
  apply Finset.sum_congr rfl
  intro i _
  have h_cast : ((‖WithLp.ofLp ψ i‖ : ℂ) ^ 2) = ↑(‖WithLp.ofLp ψ i‖ ^ 2) := by norm_cast
  rw [h_cast]
  rfl

def weightedNormSq (h : ℝ) (ψ : VecState n) : ℝ :=
  h * ‖ψ‖ ^ 2

def weightedNorm (h : ℝ) (ψ : VecState n) : ℝ :=
  Real.sqrt h * ‖ψ‖

theorem weightedNorm_sq_eq (h : ℝ) (ψ : VecState n) (hh : 0 ≤ h) :
    weightedNorm h ψ ^ 2 = weightedNormSq h ψ := by
  dsimp [weightedNormSq, weightedNorm]
  rw [mul_pow, Real.sq_sqrt hh]

theorem weightedNormSq_preserved (h : ℝ) {Uψ ψ : VecState n}
    (hpres : ‖Uψ‖ ^ 2 = ‖ψ‖ ^ 2) :
    weightedNormSq h Uψ = weightedNormSq h ψ := by
  simp [weightedNormSq, hpres]

theorem weightedNorm_preserved (h : ℝ) {Uψ ψ : VecState n}
    (hpres : ‖Uψ‖ ^ 2 = ‖ψ‖ ^ 2) :
    weightedNorm h Uψ = weightedNorm h ψ := by
  dsimp [weightedNorm]
  have h_norm_eq : ‖Uψ‖ = ‖ψ‖ := by
    have h_sqrt : Real.sqrt (‖Uψ‖ ^ 2) = Real.sqrt (‖ψ‖ ^ 2) := by rw [hpres]
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  rw [h_norm_eq]

end FiniteStateEuclideanNormBridgeV1
end NDEAMathlibGate
