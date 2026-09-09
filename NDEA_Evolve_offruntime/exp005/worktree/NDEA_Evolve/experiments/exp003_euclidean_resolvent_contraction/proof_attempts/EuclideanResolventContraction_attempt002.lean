import NDEAEvolve.Experiments.Exp002.OperatorCayley

noncomputable section

open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

private theorem cayley_eq_two_cayleyR_sub_one {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayley α A = cayleyR α A + cayleyR α A - 1 := by
  have hRight : (1 + skewPart α A) * cayleyR α A = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR α A hA
  simpa only [cayley, cayleyN, two_mul] using
    cayley_affine_of_right_inverse
      (skewPart α A) (cayleyR α A) hRight

/-- The inverse Cayley denominator is the arithmetic average of identity and
    the Cayley factor. -/
theorem cayleyR_eq_average {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    cayleyR α A = (1 / 2 : ℂ) • (1 + cayley α A) := by
  rw [cayley_eq_two_cayleyR_sub_one α A hA]
  module

/-- The same averaging identity transported to Euclidean continuous linear maps. -/
theorem cayleyR_toEuclideanCLM_eq_average {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) =
      (1 / 2 : ℂ) •
        (1 + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A)) := by
  simpa only [map_smul, map_add, map_one] using
    congrArg
      (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayleyR_eq_average α A hA)

/-- Pointwise resolvent contraction in the standard complex Euclidean norm. -/
theorem cayleyR_toEuclideanCLM_apply_norm_le {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) x‖ ≤ ‖x‖ := by
  have havg := congrArg
    (fun T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) => T x)
    (cayleyR_toEuclideanCLM_eq_average α A hA)
  have havg' :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A) x =
        (1 / 2 : ℂ) •
          (x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x) := by
    simpa using havg
  rw [havg']
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ‖(1 / 2 : ℂ) •
        (x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x)‖
        = (1 / 2 : ℝ) *
            ‖x + Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x‖ := by
              rw [norm_smul, hhalf]
    _ ≤ (1 / 2 : ℝ) *
          (‖x‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayley α A) x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖x‖ := by
      rw [cayley_preserves_norm α A hA x]
      ring

/-- Euclidean induced operator norm of the inverse denominator is at most one. -/
theorem cayleyR_toEuclideanCLM_opNorm_le_one {n : ℕ}
    (α : ℝ) (A : Mat n) (hA : A.IsHermitian) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A)‖ ≤ 1 := by
  refine (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (cayleyR α A)).opNorm_le_bound
    zero_le_one ?_
  intro x
  simpa only [one_mul] using cayleyR_toEuclideanCLM_apply_norm_le α A hA x

end NDEAEvolve.Exp003
