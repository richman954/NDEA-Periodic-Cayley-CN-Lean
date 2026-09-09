import CombinedVerification

/-! A noncommuting two-component Fourier reduction and a mesh-uniform
complete-step consistency estimate. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007

def Z : Mat 2 := ![![1, 0], ![0, -1]]
def X : Mat 2 := ![![0, 1], ![1, 0]]
def A (lambda : ℝ) : Mat 2 := (lambda : ℂ) • 1 + Z
abbrev A0 : Mat 2 := A 1
abbrev B : Mat 2 := X

theorem Z_isHermitian : Z.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Z, Matrix.conjTranspose_apply]

theorem X_isHermitian : X.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.conjTranspose_apply]

theorem A_isHermitian (lambda : ℝ) : (A lambda).IsHermitian := by
  unfold A Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
    Z_isHermitian.eq]

theorem B_isHermitian : B.IsHermitian := X_isHermitian

theorem A_noncommutes_B (lambda : ℝ) : ¬ Commute (A lambda) B := by
  intro hc
  have he := congrArg (fun M : Mat 2 => M 0 1) hc.eq
  norm_num [A, B, X, Z, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply] at he

private theorem Z_unitary : IsUnitary Z := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply]

private theorem X_unitary : IsUnitary X := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply]

theorem unitary_opNorm_le_one {n : ℕ} (M : Mat n) (hM : IsUnitary M) :
    ‖operatorOf M‖ ≤ 1 := by
  calc
    _ = ‖(1 : E n →L[ℂ] E n)‖ := by
      simpa only [mul_one] using
        CStarRing.norm_mem_unitary_mul (1 : E n →L[ℂ] E n)
          (unitary_toEuclideanCLM hM)
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

theorem Z_opNorm_le_one : ‖operatorOf Z‖ ≤ 1 :=
  unitary_opNorm_le_one Z Z_unitary

theorem B_opNorm_le_one : ‖operatorOf B‖ ≤ 1 :=
  unitary_opNorm_le_one X X_unitary

theorem A_opNorm_le_two (lambda : ℝ) (hl : 0 ≤ lambda) (hu : lambda ≤ 1) :
    ‖operatorOf (A lambda)‖ ≤ 2 := by
  have hid : ‖(1 : E 2 →L[ℂ] E 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hz := Z_opNorm_le_one
  simp only [A, operatorOf, map_add, map_smul, map_one]
  calc
    _ ≤ ‖(lambda : ℂ) • (1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := norm_add_le _ _
    _ = lambda * ‖(1 : E 2 →L[ℂ] E 2)‖ + ‖operatorOf Z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    _ ≤ lambda * 1 + 1 := add_le_add (mul_le_mul_of_nonneg_left hid hl) hz
    _ ≤ 2 := by linarith

theorem spatialSymbol_nonneg (h : ℝ) : 0 ≤ Exp006.spatialSymbol h := by
  unfold Exp006.spatialSymbol
  exact div_nonneg (by linarith [Real.cos_le_one h]) (sq_nonneg h)

theorem spatialSymbol_le_one (h : ℝ) (hh : h ≠ 0) :
    Exp006.spatialSymbol h ≤ 1 :=
  (Exp006.spatialSymbol_strictly_below_continuum h hh).le

theorem A_difference_norm_le (lambda mu : ℝ) :
    ‖operatorOf (A lambda - A mu)‖ ≤ |lambda-mu| := by
  have he : A lambda - A mu = ((lambda-mu : ℝ) : ℂ) • (1 : Mat 2) := by
    unfold A
    push_cast
    module
  rw [he]
  simp only [operatorOf, map_smul, map_one, norm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E 2))
    (abs_nonneg (lambda-mu))).trans_eq (mul_one _)

theorem Chat_affine {n : ℕ} (a : ℝ) (P : Mat n) (hP : P.IsHermitian) :
    Chat P a = Rhat P a + Rhat P a - 1 := by
  have hm : cayley a P = cayleyR a P + cayleyR a P - 1 := by
    simpa only [cayley, cayleyN, two_mul] using
      cayley_affine_of_right_inverse (skewPart a P) (cayleyR a P)
        (cayleyD_mul_cayleyR a P hP)
  simpa only [Chat, Rhat, map_add, map_sub, map_one] using
    congrArg (fun M : Mat n => operatorOf M) hm

theorem resolvent_perturbation_identity {n : ℕ} (a : ℝ) (P Q : Mat n)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    Rhat P a - Rhat Q a =
      Rhat P a * (denominatorHat Q a - denominatorHat P a) * Rhat Q a := by
  have hp := resolvent_mul_denominatorHat a P hP
  have hq : denominatorHat Q a * Rhat Q a = 1 := by
    simpa only [denominatorHat, Rhat, operatorOf, map_mul, map_one] using
      congrArg (fun M : Mat n => operatorOf M) (cayleyD_mul_cayleyR a Q hQ)
  calc
    _ = Rhat P a * (denominatorHat Q a * Rhat Q a) -
        (Rhat P a * denominatorHat P a) * Rhat Q a := by rw [hp, hq]; simp
    _ = _ := by simp only [mul_sub, sub_mul, mul_assoc]

private theorem norm_mul_bound {R : Type*} [NormedRing R]
    {P Q : R} {p q : ℝ} (hp : ‖P‖ ≤ p) (hq : ‖Q‖ ≤ q) :
    ‖P*Q‖ ≤ p*q :=
  (norm_mul_le P Q).trans
    (mul_le_mul hp hq (norm_nonneg Q) ((norm_nonneg P).trans hp))

theorem cayley_perturbation_opNorm_le {n : ℕ} (a : ℝ) (P Q : Mat n)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ‖Chat P a - Chat Q a‖ ≤ 2*|a| *‖operatorOf (P-Q)‖ := by
  have hd : denominatorHat Q a - denominatorHat P a =
      (Complex.I*(a : ℂ)) • operatorOf (Q-P) := by
    simp only [denominatorHat, cayleyD, skewPart, cscalar, operatorOf,
      map_add, map_smul, map_one, map_sub, smul_sub]
    abel
  have hn : ‖denominatorHat Q a - denominatorHat P a‖ =
      |a| *‖operatorOf (P-Q)‖ := by
    rw [hd, norm_smul]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, operatorOf, map_sub]
    rw [norm_sub_rev]
  have hr : ‖Rhat P a - Rhat Q a‖ ≤ |a| *‖operatorOf (P-Q)‖ := by
    rw [resolvent_perturbation_identity a P Q hP hQ]
    calc
      _ ≤ (1*‖denominatorHat Q a-denominatorHat P a‖)*1 :=
        norm_mul_bound
          (norm_mul_bound (cayleyR_toEuclideanCLM_opNorm_le_one a P hP) (le_refl _))
          (cayleyR_toEuclideanCLM_opNorm_le_one a Q hQ)
      _ = _ := by rw [hn]; ring
  have hc : Chat P a - Chat Q a =
      (Rhat P a-Rhat Q a)+(Rhat P a-Rhat Q a) := by
    rw [Chat_affine a P hP, Chat_affine a Q hQ]
    abel
  rw [hc]
  exact (norm_add_le _ _).trans (by linarith)

theorem cayley_opNorm_le_one {n : ℕ} (a : ℝ) (P : Mat n)
    (hP : P.IsHermitian) : ‖Chat P a‖ ≤ 1 :=
  unitary_opNorm_le_one (cayley a P) (cayley_unitary a P hP)

theorem symmetric_perturbation_opNorm_le (lambda mu k : ℝ) :
    ‖symmetricStepHat (A lambda) B k - symmetricStepHat (A mu) B k‖ ≤
      |k| *|lambda-mu| := by
  let S := Chat (A lambda) (k/4)
  let R := Chat (A mu) (k/4)
  let V := Chat B (k/2)
  have hs : ‖S‖ ≤ 1 := cayley_opNorm_le_one _ _ (A_isHermitian lambda)
  have hr : ‖R‖ ≤ 1 := cayley_opNorm_le_one _ _ (A_isHermitian mu)
  have hv : ‖V‖ ≤ 1 := cayley_opNorm_le_one _ _ B_isHermitian
  have hd : ‖S-R‖ ≤ |k| /2*|lambda-mu| := by
    calc
      _ ≤ 2*|k/4| *‖operatorOf (A lambda-A mu)‖ :=
        cayley_perturbation_opNorm_le _ _ _ (A_isHermitian lambda) (A_isHermitian mu)
      _ ≤ 2*|k/4| *|lambda-mu| :=
        mul_le_mul_of_nonneg_left (A_difference_norm_le lambda mu) (by positivity)
      _ = _ := by
        rw [abs_div, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
        ring
  have he : S*V*S-R*V*R = (S-R)*V*S+R*V*(S-R) := by
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  change ‖S*V*S-R*V*R‖ ≤ _
  rw [he]
  have h1 := norm_mul_bound (norm_mul_bound hd hv) hs
  have h2 := norm_mul_bound (norm_mul_bound hr hv) hd
  exact (norm_add_le _ _).trans (by linarith)

theorem reduced_local_error (h k : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1)
    (hk : 0 ≤ k) (hksmall : k ≤ 1/6) :
    ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k -
      exactStepHat (A0+B) (k/2)‖ ≤ k*(27000*k^2+h^2/8) := by
  have ha := A_opNorm_le_two 1 (by norm_num) (by norm_num)
  have hb := B_opNorm_le_one
  have hsum : ‖operatorOf A0‖+‖operatorOf B‖ ≤ 3 := by linarith
  have hstep : 2*|k| *(‖operatorOf A0‖+‖operatorOf B‖) ≤ 1 := by
    rw [abs_of_nonneg hk]
    have hp := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*k by positivity)
    linarith
  have ht := symmetric_cayley_exp_local_opNorm_le k A0 B
    (A_isHermitian 1) B_isHermitian hstep
  have hcube : (‖operatorOf A0‖+‖operatorOf B‖)^3 ≤ 27 := by
    calc
      _ ≤ (3:ℝ)^3 := by gcongr
      _ = 27 := by norm_num
  have htemp : ‖symmetricStepHat A0 B k-exactStepHat (A0+B) (k/2)‖ ≤
      27000*k^3 := by
    rw [abs_of_nonneg hk] at ht
    have hp := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 1000*k^3 by positivity)
    exact ht.trans (by nlinarith)
  have hspace : ‖symmetricStepHat (A (Exp006.spatialSymbol h)) B k-
      symmetricStepHat A0 B k‖ ≤ k*h^2/8 := by
    have hp := symmetric_perturbation_opNorm_le (Exp006.spatialSymbol h) 1 k
    rw [abs_of_nonneg hk] at hp
    have hc := mul_le_mul_of_nonneg_left
      (Exp006.spatialSymbol_consistency h hh hhsmall) hk
    exact hp.trans (by nlinarith)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat (A (Exp006.spatialSymbol h)) B k)
    (symmetricStepHat A0 B k) (exactStepHat (A0+B) (k/2))
  nlinarith

#print axioms A_noncommutes_B
#print axioms cayley_perturbation_opNorm_le
#print axioms reduced_local_error
end NDEAEvolve.Exp007
