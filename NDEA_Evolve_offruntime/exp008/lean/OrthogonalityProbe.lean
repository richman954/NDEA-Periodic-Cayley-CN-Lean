import Exp007Foundation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Field.GeomSum
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp006
namespace NDEAEvolve.Exp008.FourierGrid

theorem phase_nat_mul (x : ℝ) (j : ℕ) : phase ((j : ℝ) * x) = phase x ^ j := by
  unfold phase
  push_cast
  rw [mul_assoc, Complex.exp_nat_mul]

theorem phase_eq_one_iff (x : ℝ) : phase x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) * (2*Real.pi) := by
  rw [phase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hi := congrArg Complex.im hk
    simpa using hi
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    ring

theorem phase_mesh_eq_one_iff_dvd (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (r : ℤ) :
    phase ((r:ℝ)*h)=1 ↔ ((n+1:ℕ):ℤ) ∣ r := by
  have hh : h ≠ 0 := by intro hh; simp [hh] at hmesh
  rw [phase_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k, ?_⟩
    have hr : (r:ℝ) = ((n+1:ℕ):ℝ)*(k:ℝ) := by
      apply mul_right_cancel₀ hh
      rw [hk, ← hmesh]
      ring
    exact_mod_cast hr
  · rintro ⟨k,rfl⟩
    refine ⟨k, ?_⟩
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [mul_assoc, mul_comm (k:ℝ) h, ← mul_assoc, hmesh]
    ring

theorem phase_sum_zero (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (r : ℤ)
    (hr : ¬ ((n+1:ℕ):ℤ) ∣ r) :
    (∑ j : Fin (n+1), phase ((r:ℝ)*((j.val:ℝ)*h)))=0 := by
  have hne : phase ((r:ℝ)*h) ≠ 1 := by
    simpa [phase_mesh_eq_one_iff_dvd n h hmesh r] using hr
  have hp : phase ((r:ℝ)*h)^(n+1)=1 := by
    rw [← phase_nat_mul]
    have he : ((n+1:ℕ):ℝ)*((r:ℝ)*h)=(r:ℝ)*(2*Real.pi) := by rw [← hmesh]; ring
    rw [he]
    exact (phase_eq_one_iff _).mpr ⟨r,rfl⟩
  calc
    _ = ∑ j : Fin (n+1), phase ((r:ℝ)*h)^j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← phase_nat_mul]
      congr 1
      ring
    _ = 0 := by rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne, hp]; simp

theorem band_difference_not_dvd (M n : ℕ) (m l : ℤ)
    (hm : |(m:ℝ)| ≤ (M:ℝ)) (hl : |(l:ℝ)| ≤ (M:ℝ))
    (hband : 2*M < n+1) (hne : m ≠ l) : ¬ ((n+1:ℕ):ℤ) ∣ l-m := by
  rintro ⟨k,hk⟩
  have hM : (2:ℝ)*M < (n+1:ℕ) := by exact_mod_cast hband
  have hd : (0:ℝ)<(n+1:ℕ) := by positivity
  have hkr : (l:ℝ)-(m:ℝ)=((n+1:ℕ):ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hsub : |(l:ℝ)-(m:ℝ)| ≤ 2*(M:ℝ) := (abs_sub _ _).trans (by linarith)
  have habsk : |(k:ℝ)| < 1 := by
    rw [hkr, abs_mul, abs_of_pos hd] at hsub
    nlinarith
  have hkb : -1 < k ∧ k < 1 := by exact_mod_cast (abs_lt.mp habsk)
  have hk0 : k=0 := by omega
  simp [hk0] at hk
  omega

end NDEAEvolve.Exp008.FourierGrid
