import ActualCayleyCertificate
import OrderedStageBounds

/-! Potential perturbation for the actual ordered Cayley recurrence.
The resolvent algebra and estimate adapt the sealed Exp007
`ReducedNoncommuting.lean` proof from `Fin n` to an arbitrary finite index.
All matrix sizes are measured through the induced Euclidean operator norm.
The common outer A stages need no commutation or mesh-dependent estimate. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem cp_step_norm (a : ℝ) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (u : Vec ι) : ‖step a P u‖ = ‖u‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (step_mem_unitary a P hP) u

theorem step_opNorm_le_one (a : ℝ) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) : ‖step a P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [cp_step_norm a P hP, one_mul]

theorem step_resolvent_affine (a : ℝ) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) :
    step a P = op (resolvent a P) + op (resolvent a P) - 1 := by
  have hm : cayleyMatrix a P = resolvent a P + resolvent a P - 1 := by
    simpa only [cayleyMatrix, num, two_mul] using
      cayley_affine_of_right_inverse ((Complex.I * (a : ℂ)) • P)
        (resolvent a P) (den_mul_resolvent a P hP)
  simpa only [step, map_add, map_sub, map_one] using congrArg op hm

theorem resolvent_opNorm_le_one (a : ℝ) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) : ‖op (resolvent a P)‖ ≤ 1 := by
  have hr : op (resolvent a P) = (1 / 2 : ℂ) • (step a P + 1) := by
    rw [step_resolvent_affine a P hP]
    module
  have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hr, norm_smul, hc]
  have ht := norm_add_le (step a P) (1 : Vec ι →L[ℂ] Vec ι)
  have hs := step_opNorm_le_one a P hP
  have hi : ‖(1 : Vec ι →L[ℂ] Vec ι)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

theorem resolvent_difference_identity (a : ℝ) (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    op (resolvent a P) - op (resolvent a Q) =
      op (resolvent a P) * (op (den a Q) - op (den a P)) * op (resolvent a Q) := by
  have hp : op (resolvent a P) * op (den a P) = 1 := by
    rw [← map_mul, resolvent_mul_den a P hP, map_one]
  have hq : op (den a Q) * op (resolvent a Q) = 1 := by
    rw [← map_mul, den_mul_resolvent a Q hQ, map_one]
  calc
    _ = op (resolvent a P) * (op (den a Q) * op (resolvent a Q)) -
        (op (resolvent a P) * op (den a P)) * op (resolvent a Q) := by
      rw [hp, hq]
      simp
    _ = _ := by simp only [mul_sub, sub_mul, mul_assoc]

private theorem cp_norm_mul_bound {R : Type*} [NormedRing R]
    {P Q : R} {p q : ℝ} (hp : ‖P‖ ≤ p) (hq : ‖Q‖ ≤ q) :
    ‖P * Q‖ ≤ p * q :=
  (norm_mul_le P Q).trans
    (mul_le_mul hp hq (norm_nonneg Q) ((norm_nonneg P).trans hp))

theorem step_perturbation_opNorm_le (a : ℝ) (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ‖step a P - step a Q‖ ≤ 2 * |a| * ‖op (P - Q)‖ := by
  have hd : op (den a Q) - op (den a P) =
      (Complex.I * (a : ℂ)) • op (Q - P) := by
    simp only [den, map_add, map_smul, map_one, map_sub, smul_sub]
    abel
  have hn : ‖op (den a Q) - op (den a P)‖ = |a| * ‖op (P - Q)‖ := by
    rw [hd, norm_smul]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, map_sub]
    rw [norm_sub_rev]
  have hr : ‖op (resolvent a P) - op (resolvent a Q)‖ ≤
      |a| * ‖op (P - Q)‖ := by
    rw [resolvent_difference_identity a P Q hP hQ]
    calc
      _ ≤ (1 * ‖op (den a Q) - op (den a P)‖) * 1 :=
        cp_norm_mul_bound
          (cp_norm_mul_bound (resolvent_opNorm_le_one a P hP) (le_refl _))
          (resolvent_opNorm_le_one a Q hQ)
      _ = _ := by rw [hn]; ring
  have hc : step a P - step a Q =
      (op (resolvent a P) - op (resolvent a Q)) +
        (op (resolvent a P) - op (resolvent a Q)) := by
    rw [step_resolvent_affine a P hP, step_resolvent_affine a Q hQ]
    abel
  rw [hc]
  exact (norm_add_le _ _).trans (by linarith)

theorem orderedCayleyEndpoint_sub_norm (A B : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (u z : Vec ι) :
    ‖orderedCayleyEndpoint A B k u - orderedCayleyEndpoint A B k z‖ = ‖u - z‖ := by
  have he : orderedCayleyEndpoint A B k u - orderedCayleyEndpoint A B k z =
      orderedCayleyEndpoint A B k (u - z) := by
    simp only [orderedCayleyEndpoint, map_sub]
  rw [he, orderedCayleyEndpoint_norm A B k hA hB]

/-- Changing only the potential stage costs |k| times the generator change.
The initial-state discrepancy is retained without an equality assumption. -/
theorem orderedCayleyEndpoint_potential_perturbation (A B C : Matrix ι ι ℂ) (k : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (u z : Vec ι) :
    ‖orderedCayleyEndpoint A B k u - orderedCayleyEndpoint A C k z‖ ≤
      ‖u - z‖ + |k| * ‖op (B - C)‖ * ‖z‖ := by
  have hsame : ‖orderedCayleyEndpoint A B k z - orderedCayleyEndpoint A C k z‖ ≤
      |k| * ‖op (B - C)‖ * ‖z‖ := by
    unfold orderedCayleyEndpoint
    rw [← map_sub, cp_step_norm (k / 4) A hA]
    have hd := step_perturbation_opNorm_le (k / 2) B C hB hC
    have he : 2 * |k / 2| = |k| := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      ring
    rw [he] at hd
    calc
      _ ≤ ‖step (k / 2) B - step (k / 2) C‖ * ‖step (k / 4) A z‖ :=
        (step (k / 2) B - step (k / 2) C).le_opNorm _
      _ ≤ (|k| * ‖op (B - C)‖) * ‖step (k / 4) A z‖ :=
        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = _ := by rw [cp_step_norm (k / 4) A hA]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (orderedCayleyEndpoint A B k u) (orderedCayleyEndpoint A B k z)
    (orderedCayleyEndpoint A C k z)
  rw [orderedCayleyEndpoint_sub_norm A B k hA hB] at ht
  exact ht.trans (add_le_add le_rfl hsame)

theorem actualCayleyTrajectory_norm (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (y₀ : Vec ι) (k : ℕ → ℝ) (N : ℕ) :
    ‖actualCayleyTrajectory A B y₀ k N‖ = ‖y₀‖ := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [actualCayleyTrajectory_succ, orderedCayleyEndpoint_norm A B (k N) hA hB, ih]

/-- A dimension-independent finite-trajectory bound, valid for arbitrary
signed variable steps. No generator commutativity or refinement is asserted. -/
theorem actualCayleyTrajectory_potential_perturbation (A B C : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (u₀ z₀ : Vec ι) (k : ℕ → ℝ) (N : ℕ) :
    ‖actualCayleyTrajectory A B u₀ k N - actualCayleyTrajectory A C z₀ k N‖ ≤
      ‖u₀ - z₀‖ + (∑ j ∈ Finset.range N, |k j|) * ‖op (B - C)‖ * ‖z₀‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [actualCayleyTrajectory_succ, actualCayleyTrajectory_succ]
    have hs := orderedCayleyEndpoint_potential_perturbation A B C (k N) hA hB hC
      (actualCayleyTrajectory A B u₀ k N) (actualCayleyTrajectory A C z₀ k N)
    rw [actualCayleyTrajectory_norm A C hA hC z₀ k N] at hs
    calc
      _ ≤ ‖actualCayleyTrajectory A B u₀ k N - actualCayleyTrajectory A C z₀ k N‖ +
          |k N| * ‖op (B - C)‖ * ‖z₀‖ := hs
      _ ≤ (‖u₀ - z₀‖ + (∑ j ∈ Finset.range N, |k j|) * ‖op (B - C)‖ * ‖z₀‖) +
          |k N| * ‖op (B - C)‖ * ‖z₀‖ := add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_range_succ]; ring

#print axioms step_opNorm_le_one
#print axioms step_resolvent_affine
#print axioms resolvent_opNorm_le_one
#print axioms resolvent_difference_identity
#print axioms step_perturbation_opNorm_le
#print axioms orderedCayleyEndpoint_sub_norm
#print axioms orderedCayleyEndpoint_potential_perturbation
#print axioms actualCayleyTrajectory_norm
#print axioms actualCayleyTrajectory_potential_perturbation

end NDEAEvolve.Exp016
