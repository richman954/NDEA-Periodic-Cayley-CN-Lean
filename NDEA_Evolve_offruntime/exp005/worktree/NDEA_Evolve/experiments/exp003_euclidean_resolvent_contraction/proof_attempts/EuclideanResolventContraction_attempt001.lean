import NDEAEvolve.Experiments.Exp002.OperatorCayley

noncomputable section

open Matrix

namespace NDEAEvolve
namespace Exp003

open Exp002

abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)

def Rhat {n : ℕ} (α : ℝ) (A : Exp002.Mat n) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A)

def Chat {n : ℕ} (α : ℝ) (A : Exp002.Mat n) : E n →L[ℂ] E n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A)

theorem cayley_affine_matrix {n : ℕ} (α : ℝ) (A : Exp002.Mat n)
    (hA : A.IsHermitian) :
    cayley α A = (2 : Exp002.Mat n) * cayleyR α A - 1 := by
  change (1 - skewPart α A) * cayleyR α A = _
  exact cayley_affine_of_right_inverse (skewPart α A) (cayleyR α A)
    (by simpa [cayleyD] using cayleyD_mul_cayleyR α A hA)

theorem cayleyR_averaging_matrix {n : ℕ} (α : ℝ) (A : Exp002.Mat n)
    (hA : A.IsHermitian) :
    cayleyR α A = (1 / 2 : ℂ) • (1 + cayley α A) := by
  rw [cayley_affine_matrix α A hA]
  ext i j
  simp [Matrix.one_apply]
  ring

theorem resolvent_averaging {n : ℕ} (α : ℝ) (A : Exp002.Mat n)
    (hA : A.IsHermitian) :
    Rhat α A = (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (E n) + Chat α A) := by
  unfold Rhat Chat
  simpa only [map_smul, map_add, map_one] using
    congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n))
      (cayleyR_averaging_matrix α A hA)

theorem resolvent_pointwise_nonexpansive {n : ℕ} (α : ℝ) (A : Exp002.Mat n)
    (hA : A.IsHermitian) (x : E n) :
    ‖Rhat α A x‖ ≤ ‖x‖ := by
  rw [resolvent_averaging α A hA]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, norm_smul]
  rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  calc
    (1 / 2 : ℝ) * ‖x + Chat α A x‖ ≤
        (1 / 2 : ℝ) * (‖x‖ + ‖Chat α A x‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖x‖ := by
      rw [show ‖Chat α A x‖ = ‖x‖ by
        exact cayley_preserves_norm α A hA x]
      ring

theorem resolvent_opNorm_le_one {n : ℕ} (α : ℝ) (A : Exp002.Mat n)
    (hA : A.IsHermitian) :
    ‖Rhat α A‖ ≤ 1 := by
  apply (Rhat α A).opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using resolvent_pointwise_nonexpansive α A hA x

end Exp003
end NDEAEvolve
