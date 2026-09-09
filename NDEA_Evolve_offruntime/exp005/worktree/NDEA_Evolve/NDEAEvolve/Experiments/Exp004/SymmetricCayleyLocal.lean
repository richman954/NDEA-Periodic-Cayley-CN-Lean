import NDEAEvolve.Experiments.Exp003.ContinuousExponentialComparison
import Mathlib.Tactic.GCongr

/-!
# Cubic local consistency of the symmetric Cayley composition

The three factors approximate exp(-i h A/2), exp(-i h B), exp(-i h A/2),
respectively: their Cayley parameters are h/4, h/2, h/4.
The ordered quadratic terms cancel without a commutativity hypothesis.
Every analytic estimate uses the induced continuous-endomorphism norm.
-/

noncomputable section

open NDEAEvolve.Exp002 NDEAEvolve.Exp003

namespace NDEAEvolve.Exp004

abbrev symmetricStepHat {n : ℕ} (A B : Mat n) (h : ℝ) : E n →L[ℂ] E n :=
  Chat A (h / 4) * Chat B (h / 2) * Chat A (h / 4)

private def linPart {R : Type*} [Ring R] (X : R) : R := -(X + X)
private def quadPart {R : Type*} [Ring R] (X : R) : R := X ^ 2 + X ^ 2
private def cayleyPoly {R : Type*} [Ring R] (X : R) : R :=
  1 + linPart X + quadPart X

private theorem cayleyPoly_eq {R : Type*} [Ring R] (X : R) :
    cayleyPoly X = 1 - X - X + X ^ 2 + X ^ 2 := by
  unfold cayleyPoly linPart quadPart
  noncomm_ring

/-- All degree-zero, degree-one, and degree-two terms agree. The four
displayed groups on the right have degree at least three. -/
private theorem symmetric_quadratic_cancellation {R : Type*} [Ring R]
    (X Y : R) :
    cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly (X + X + Y) =
      (linPart X * quadPart Y + quadPart X * linPart Y +
        quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * linPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * quadPart X := by
  unfold cayleyPoly linPart quadPart
  noncomm_ring

private theorem norm_mul_bound {R : Type*} [NormedRing R]
    {X Y : R} {x y : ℝ} (hX : ‖X‖ ≤ x) (hY : ‖Y‖ ≤ y) :
    ‖X * Y‖ ≤ x * y :=
  (norm_mul_le X Y).trans
    (mul_le_mul hX hY (norm_nonneg Y) ((norm_nonneg X).trans hX))

private theorem linPart_norm_le {R : Type*} [NormedRing R]
    {X : R} {r : ℝ} (hX : ‖X‖ ≤ r) : ‖linPart X‖ ≤ 2 * r := by
  unfold linPart
  rw [norm_neg]
  exact (norm_add_le X X).trans (by linarith)

private theorem quadPart_norm_le {R : Type*} [NormedRing R]
    {X : R} {r : ℝ} (_hr : 0 ≤ r) (hX : ‖X‖ ≤ r) :
    ‖quadPart X‖ ≤ 2 * r ^ 2 := by
  have hp : ‖X ^ 2‖ ≤ r ^ 2 := by
    calc
      _ ≤ ‖X‖ ^ 2 := norm_pow_le' X (by decide)
      _ ≤ r ^ 2 := by gcongr
  unfold quadPart
  exact (norm_add_le (X ^ 2) (X ^ 2)).trans (by linarith)

private theorem cayleyPoly_norm_le_five {R : Type*} [NormedRing R]
    (hOne : ‖(1 : R)‖ ≤ 1) {X : R} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hX : ‖X‖ ≤ r) :
    ‖cayleyPoly X‖ ≤ 5 := by
  have hl := linPart_norm_le hX
  have hq := quadPart_norm_le hr hX
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  unfold cayleyPoly
  calc
    ‖1 + linPart X + quadPart X‖ ≤ ‖1 + linPart X‖ + ‖quadPart X‖ :=
      norm_add_le _ _
    _ ≤ (‖(1 : R)‖ + ‖linPart X‖) + ‖quadPart X‖ :=
      add_le_add (norm_add_le (1 : R) (linPart X)) (le_refl ‖quadPart X‖)
    _ ≤ 5 := by linarith

/-- A norm estimate for the explicitly ordered polynomial remainder. -/
private theorem symmetric_quadratic_remainder_norm_le {R : Type*} [NormedRing R]
    (hOne : ‖(1 : R)‖ ≤ 1) {X Y : R} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r) :
    ‖cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly (X + X + Y)‖ ≤
      100 * r ^ 3 := by
  have hlX := linPart_norm_le hX
  have hlY := linPart_norm_le hY
  have hqX := quadPart_norm_le hr hX
  have hqY := quadPart_norm_le hr hY
  have hPX := cayleyPoly_norm_le_five hOne hr hr1 hX
  have hr4 : r ^ 4 ≤ r ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ r ^ 3 by positivity)
    nlinarith
  have hpair : ‖linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y‖ ≤ 12 * r ^ 3 := by
    have h1 := norm_mul_bound hlX hqY
    have h2 := norm_mul_bound hqX hlY
    have h3 := norm_mul_bound hqX hqY
    have ha := norm_add_le (linPart X * quadPart Y) (quadPart X * linPart Y)
    have hb := norm_add_le (linPart X * quadPart Y + quadPart X * linPart Y)
      (quadPart X * quadPart Y)
    nlinarith
  have hlin : ‖linPart X + linPart Y‖ ≤ 4 * r :=
    (norm_add_le _ _).trans (by linarith)
  have hquad : ‖quadPart X + linPart X * linPart Y + quadPart Y‖ ≤ 8 * r ^ 2 := by
    have hm := norm_mul_bound hlX hlY
    have ha := norm_add_le (quadPart X) (linPart X * linPart Y)
    have hb := norm_add_le (quadPart X + linPart X * linPart Y) (quadPart Y)
    nlinarith
  have h1 := norm_mul_bound hpair hPX
  have h2 := norm_mul_bound hlin hqX
  have h3 := norm_mul_bound hquad hlX
  have h4 := norm_mul_bound hquad hqX
  rw [symmetric_quadratic_cancellation]
  have ha := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X)
    ((linPart X + linPart Y) * quadPart X)
  have hb := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X)
    ((quadPart X + linPart X * linPart Y + quadPart Y) * linPart X)
  have hc := norm_add_le
    ((linPart X * quadPart Y + quadPart X * linPart Y +
      quadPart X * quadPart Y) * cayleyPoly X +
      (linPart X + linPart Y) * quadPart X +
      (quadPart X + linPart X * linPart Y + quadPart Y) * linPart X)
    ((quadPart X + linPart X * linPart Y + quadPart Y) * quadPart X)
  nlinarith

private theorem sandwich_replacement_norm_le {R : Type*} [NormedRing R]
    {S T P Q : R} {d : ℝ}
    (hS : ‖S‖ ≤ 1) (hT : ‖T‖ ≤ 1)
    (hP : ‖P‖ ≤ 5) (hQ : ‖Q‖ ≤ 5)
    (hSP : ‖S - P‖ ≤ d) (hTQ : ‖T - Q‖ ≤ d) :
    ‖S * T * S - P * Q * P‖ ≤ 31 * d := by
  have hid : S * T * S - P * Q * P =
      (S - P) * T * S + P * (T - Q) * S + P * Q * (S - P) := by
    noncomm_ring
  have h1 := norm_mul_bound (norm_mul_bound hSP hT) hS
  have h2 := norm_mul_bound (norm_mul_bound hP hTQ) hS
  have h3 := norm_mul_bound (norm_mul_bound hP hQ) hSP
  rw [hid]
  have ha := norm_add_le ((S - P) * T * S) (P * (T - Q) * S)
  have hb := norm_add_le ((S - P) * T * S + P * (T - Q) * S) (P * Q * (S - P))
  nlinarith

private theorem cayley_norm_le_one {n : ℕ}
    (a : ℝ) (H : Mat n) (hH : H.IsHermitian) : ‖Chat H a‖ ≤ 1 := by
  have hu := unitary_toEuclideanCLM (cayley_unitary a H hH)
  calc
    ‖Chat H a‖ = ‖(1 : E n →L[ℂ] E n)‖ := by
      simpa only [mul_one] using
        CStarRing.norm_mem_unitary_mul (1 : E n →L[ℂ] E n) hu
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

/-- The sum generator is the sum of the three ordered substep generators. -/
private theorem symmetric_skew_sum {n : ℕ} (h : ℝ) (A B : Mat n) :
    skewHat A (h / 4) + skewHat A (h / 4) + skewHat B (h / 2) =
      skewHat (A + B) (h / 2) := by
  simp only [skewHat, operatorOf, map_add, smul_add]
  push_cast
  module

/-- A cubic local error bound for symmetric Cayley splitting, for arbitrary
finite Hermitian generators, including dimension zero and either time sign. -/
theorem symmetric_cayley_exp_local_opNorm_le {n : ℕ}
    (h : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hstep : 2 * |h| * (‖operatorOf A‖ + ‖operatorOf B‖) ≤ 1) :
    ‖symmetricStepHat A B h - exactStepHat (A + B) (h / 2)‖ ≤
      1000 * |h| ^ 3 * (‖operatorOf A‖ + ‖operatorOf B‖) ^ 3 := by
  let r : ℝ := |h| * (‖operatorOf A‖ + ‖operatorOf B‖)
  let X := skewHat A (h / 4)
  let Y := skewHat B (h / 2)
  let W := skewHat (A + B) (h / 2)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by dsimp [r]; nlinarith [hstep]
  have hr1 : r ≤ 1 := by linarith
  have hsum : ‖operatorOf (A + B)‖ ≤ ‖operatorOf A‖ + ‖operatorOf B‖ := by
    simpa only [operatorOf, map_add] using norm_add_le (operatorOf A) (operatorOf B)
  have hpa : |h| * ‖operatorOf A‖ ≤ r := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (abs_nonneg h)
  have hpb : |h| * ‖operatorOf B‖ ≤ r := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (abs_nonneg h)
  have hpw : |h| * ‖operatorOf (A + B)‖ ≤ r :=
    mul_le_mul_of_nonneg_left hsum (abs_nonneg h)
  have hX : ‖X‖ ≤ r := by
    change ‖skewHat A (h / 4)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (4 : ℝ) by norm_num)]
    nlinarith only [hpa, hr]
  have hY : ‖Y‖ ≤ r := by
    change ‖skewHat B (h / 2)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpb, hr]
  have hW : ‖W‖ ≤ r := by
    change ‖skewHat (A + B) (h / 2)‖ ≤ r
    rw [skewHat_norm, abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpw, hr]
  have hOne : ‖(1 : E n →L[ℂ] E n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hPX := cayleyPoly_norm_le_five hOne hr hr1 hX
  have hPY := cayleyPoly_norm_le_five hOne hr hr1 hY
  have hCX : ‖Chat A (h / 4) - cayleyPoly X‖ ≤ 2 * r ^ 3 := by
    rw [cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖X‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 4) A hA
      _ ≤ 2 * r ^ 3 := by gcongr
  have hCY : ‖Chat B (h / 2) - cayleyPoly Y‖ ≤ 2 * r ^ 3 := by
    rw [cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖Y‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 2) B hB
      _ ≤ 2 * r ^ 3 := by gcongr
  have hreplace : ‖symmetricStepHat A B h - cayleyPoly X * cayleyPoly Y * cayleyPoly X‖ ≤
      62 * r ^ 3 := by
    have hb := sandwich_replacement_norm_le
      (cayley_norm_le_one (h / 4) A hA) (cayley_norm_le_one (h / 2) B hB)
      hPX hPY hCX hCY
    change ‖symmetricStepHat A B h - cayleyPoly X * cayleyPoly Y * cayleyPoly X‖ ≤
      31 * (2 * r ^ 3) at hb
    nlinarith
  have hcancel : ‖cayleyPoly X * cayleyPoly Y * cayleyPoly X - cayleyPoly W‖ ≤
      100 * r ^ 3 := by
    have hb := symmetric_quadratic_remainder_norm_le hOne hr hr1 hX hY
    have hid : X + X + Y = W := symmetric_skew_sum h A B
    rwa [hid] at hb
  have hCW : ‖cayleyPoly W - Chat (A + B) (h / 2)‖ ≤ 2 * r ^ 3 := by
    rw [norm_sub_rev, cayleyPoly_eq]
    calc
      _ ≤ 2 * ‖W‖ ^ 3 := cayley_quadratic_remainder_opNorm_le (h / 2) (A + B) (hA.add hB)
      _ ≤ 2 * r ^ 3 := by gcongr
  have hs : 4 * |h / 2| * ‖operatorOf (A + B)‖ ≤ 1 := by
    rw [abs_div, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
    nlinarith only [hpw, hrhalf]
  have hCE : ‖Chat (A + B) (h / 2) - exactStepHat (A + B) (h / 2)‖ ≤
      18 * r ^ 3 := by
    calc
      _ ≤ 18 * |h / 2| ^ 3 * ‖operatorOf (A + B)‖ ^ 3 :=
        cayley_exp_local_opNorm_le (h / 2) (A + B) (hA.add hB) hs
      _ = 18 * ‖W‖ ^ 3 := by change _ = 18 * ‖skewHat (A + B) (h / 2)‖ ^ 3; rw [skewHat_norm]; ring
      _ ≤ 18 * r ^ 3 := by gcongr
  have htri1 := norm_sub_le_norm_sub_add_norm_sub
    (symmetricStepHat A B h) (cayleyPoly X * cayleyPoly Y * cayleyPoly X)
    (exactStepHat (A + B) (h / 2))
  have htri2 := norm_sub_le_norm_sub_add_norm_sub
    (cayleyPoly X * cayleyPoly Y * cayleyPoly X) (cayleyPoly W)
    (exactStepHat (A + B) (h / 2))
  have htri3 := norm_sub_le_norm_sub_add_norm_sub
    (cayleyPoly W) (Chat (A + B) (h / 2)) (exactStepHat (A + B) (h / 2))
  calc
    _ ≤ 182 * r ^ 3 := by linarith
    _ ≤ 1000 * r ^ 3 := by nlinarith [pow_nonneg hr 3]
    _ = _ := by dsimp [r]; ring

end NDEAEvolve.Exp004

#check @NDEAEvolve.Exp004.symmetric_cayley_exp_local_opNorm_le
#print axioms NDEAEvolve.Exp004.symmetric_cayley_exp_local_opNorm_le
