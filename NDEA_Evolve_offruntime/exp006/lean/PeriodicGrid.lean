import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Minimal finite periodic grid, Hermitian centered negative Laplacian,
and its action on samples of a periodic function.  The endpoint wrap is
proved explicitly from the period and mesh identity. -/

noncomputable section
open Matrix Complex
namespace NDEAEvolve.Exp006.PeriodicGrid

abbrev next {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) := finRotate (n + 1) i

abbrev prev {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  (finRotate (n + 1)).symm i

def sample {n : ℕ} (h : ℝ) (f : ℝ → ℂ) : Fin (n + 1) → ℂ :=
  fun i => f ((i.val : ℝ) * h)

def shiftMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (finRotate (n + 1)).permMatrix ℂ

/-- Centered negative second difference, including the periodic corner entries. -/
def laplacian (n : ℕ) (h : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ((h : ℂ) ^ 2)⁻¹ •
    ((2 : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      shiftMatrix n - (shiftMatrix n)ᴴ)

theorem isHermitian (n : ℕ) (h : ℝ) : (laplacian n h).IsHermitian := by
  unfold laplacian Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one,
    star_inv₀, star_pow, Complex.star_def, Complex.conj_ofReal,
    map_ofNat]
  congr 1
  abel

theorem laplacian_mulVec {n : ℕ} (h : ℝ) (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) :
    (laplacian n h).mulVec v i =
      (2 * v i - v (next i) - v (prev i)) / (h : ℂ)^2 := by
  simp only [laplacian, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, shiftMatrix, Matrix.conjTranspose_permMatrix,
    Matrix.permMatrix_mulVec, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Function.comp_apply, Equiv.Perm.inv_def, next, prev]
  ring

theorem sample_next {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) : sample h f (next i) = f ((i.val : ℝ) * h + h) := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [next, finRotate_last, sample, Fin.val_zero, Fin.val_last,
      Nat.cast_zero, zero_mul]
    have hcoord : (n : ℝ) * h + h = L := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hmesh
    rw [hcoord]
    simpa using (hf 0).symm
  · change f (((finRotate (n + 1) i).val : ℝ) * h) = _
    rw [coe_finRotate_of_ne_last hi, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem sample_prev {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) : sample h f (prev i) = f ((i.val : ℝ) * h - h) := by
  by_cases hi : i = 0
  · subst i
    have hprev : prev (0 : Fin (n + 1)) = Fin.last n := by
      apply (finRotate (n + 1)).injective
      simp only [prev, Equiv.apply_symm_apply, finRotate_last]
    rw [hprev]
    simp only [sample, Fin.val_last, Fin.val_zero, Nat.cast_zero, zero_mul, zero_sub]
    have hcoord : -h + L = (n : ℝ) * h := by
      calc
        -h + L = -h + (((n + 1 : ℕ) : ℝ)) * h := by rw [hmesh]
        _ = (n : ℝ) * h := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [← hcoord]
    exact hf (-h)
  · change f ((((finRotate (n + 1)).symm i).val : ℝ) * h) = _
    have hival : i.val ≠ 0 := by
      intro hzero
      apply hi
      apply Fin.ext
      simpa using hzero
    have hone : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hival
    rw [coe_finRotate_symm_of_ne_zero hi, Nat.cast_sub hone, Nat.cast_one]
    congr 1
    ring

/-- The matrix really applies the unwrapped centered stencil to periodic samples,
including the first and last rows. No condition on the sample function is omitted. -/
theorem matrix_sample_stencil {n : ℕ} (L h : ℝ) (f : ℝ → ℂ)
    (hf : Function.Periodic f L) (hmesh : ((n + 1 : ℕ) : ℝ) * h = L)
    (i : Fin (n + 1)) :
    (laplacian n h).mulVec (sample h f) i =
      (2 * f ((i.val : ℝ) * h) - f ((i.val : ℝ) * h + h) -
        f ((i.val : ℝ) * h - h)) / (h : ℂ)^2 := by
  rw [laplacian_mulVec, sample_next L h f hf hmesh,
    sample_prev L h f hf hmesh]
  rfl

#print axioms isHermitian
#print axioms laplacian_mulVec
#print axioms sample_next
#print axioms sample_prev
#print axioms matrix_sample_stencil

end NDEAEvolve.Exp006.PeriodicGrid
