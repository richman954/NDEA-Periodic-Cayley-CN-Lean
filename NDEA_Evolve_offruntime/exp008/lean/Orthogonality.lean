import FourierGrid
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Field.GeomSum

/-! Exact discrete Fourier orthogonality and Parseval on an alias-free finite band. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
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

theorem phase_conj (x : ℝ) : starRingEnd ℂ (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem mode_product (m l : ℤ) (x : ℝ) (u v : ℂ) :
    (phase ((l:ℝ)*x)*v)*starRingEnd ℂ (phase ((m:ℝ)*x)*u) =
      phase (((l-m:ℤ):ℝ)*x)*(v*starRingEnd ℂ u) := by
  rw [map_mul]
  calc
    _ = (phase ((l:ℝ)*x)*starRingEnd ℂ (phase ((m:ℝ)*x)))*
        (v*starRingEnd ℂ u) := by ring
    _ = _ := by
      rw [phase_conj, ← phase_add]
      congr 2
      push_cast
      ring

theorem modeLift_inner_eq_zero (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (m l : ℤ)
    (hne : ¬ ((n+1:ℕ):ℤ) ∣ l-m) (u v : E 2) :
    inner ℂ (modeLiftCLM n h m u) (modeLiftCLM n h l v) = 0 := by
  change (∑ p : Grid n, (phase ((l:ℝ)*((p.1.val:ℝ)*h))*v p.2)*
    starRingEnd ℂ (phase ((m:ℝ)*((p.1.val:ℝ)*h))*u p.2))=0
  rw [Fintype.sum_prod_type]
  simp only [mode_product]
  have he : (∑ i : Fin (n+1), ∑ b : Fin 2,
      phase (((l-m:ℤ):ℝ)*((i.val:ℝ)*h))*(v b*starRingEnd ℂ (u b))) =
      (∑ i : Fin (n+1), phase (((l-m:ℤ):ℝ)*((i.val:ℝ)*h)))*
        (∑ b : Fin 2, v b*starRingEnd ℂ (u b)) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [he, phase_sum_zero n h hmesh (l-m) hne, zero_mul]

def AliasFree (n : ℕ) (S : Finset ℤ) : Prop :=
  ∀ m ∈ S, ∀ l ∈ S, m ≠ l → ¬ ((n+1:ℕ):ℤ) ∣ l-m

theorem aliasFree_of_band (M n : ℕ) (S : Finset ℤ)
    (hband : 2*M < n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ)) : AliasFree n S := by
  intro m hm l hl hne
  exact band_difference_not_dvd M n m l (hS m hm) (hS l hl) hband hne

theorem superposition_norm_sq (n : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hS : AliasFree n S) (a : ℤ → E 2) :
    ‖superpositionLift n h S a‖^2 = ((n+1:ℕ):ℝ) * ∑ m ∈ S, ‖a m‖^2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [superpositionLift]
  | @insert m S hm ih =>
    have hsub : AliasFree n S := by
      intro l hl r hr hne
      exact hS l (Finset.mem_insert_of_mem hl) r (Finset.mem_insert_of_mem hr) hne
    have horth : inner ℂ (modeLiftCLM n h m (a m)) (superpositionLift n h S a) = 0 := by
      unfold superpositionLift
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro l hl
      exact modeLift_inner_eq_zero n h hmesh m l
        (hS m (Finset.mem_insert_self _ _) l (Finset.mem_insert_of_mem hl)
          (by intro he; exact hm (he.symm ▸ hl))) (a m) (a l)
    have hins : superpositionLift n h (insert m S) a =
        modeLiftCLM n h m (a m)+superpositionLift n h S a := by
      simp [superpositionLift, hm]
    have hpy : ‖modeLiftCLM n h m (a m)+superpositionLift n h S a‖^2 =
        ‖modeLiftCLM n h m (a m)‖^2+‖superpositionLift n h S a‖^2 := by
      simpa only [← pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [hins, hpy,
      modeLiftCLM_apply, modeLift_norm_sq, ih hsub, Finset.sum_insert hm]
    ring

theorem superposition_weighted_norm (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hS : AliasFree n S) (a : ℤ → E 2) :
    Real.sqrt h * ‖superpositionLift n h S a‖ =
      Real.sqrt (2*Real.pi) * Real.sqrt (∑ m ∈ S, ‖a m‖^2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),
    Real.sq_sqrt (Finset.sum_nonneg (fun m _ => sq_nonneg ‖a m‖)),
    superposition_norm_sq n h hmesh S hS a]
  rw [← mul_assoc, mul_comm h, hmesh]

theorem band_superposition_weighted_norm (M n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (S : Finset ℤ)
    (hband : 2*M < n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ)) (a : ℤ → E 2) :
    Real.sqrt h * ‖superpositionLift n h S a‖ =
      Real.sqrt (2*Real.pi) * Real.sqrt (∑ m ∈ S, ‖a m‖^2) :=
  superposition_weighted_norm n h hh hmesh S (aliasFree_of_band M n S hband hS) a

end NDEAEvolve.Exp008.FourierGrid
