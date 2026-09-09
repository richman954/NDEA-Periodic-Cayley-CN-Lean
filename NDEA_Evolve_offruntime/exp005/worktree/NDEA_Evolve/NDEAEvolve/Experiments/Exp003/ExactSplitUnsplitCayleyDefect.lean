import NDEAEvolve.Experiments.Exp003.ExactOrderDefectNormBound

/-!
# Exact split-versus-unsplit Cayley defect

This Step-3 module proves the exact local defect identity for two Cayley
factors and its induced Euclidean operator-norm estimate.  The proof is
purely finite-dimensional and algebraic; the only analytic input is the
Step-1 resolvent contraction theorem.
-/

noncomputable section

open NDEAEvolve.Exp002

namespace NDEAEvolve.Exp003

/-! ## Pure noncommutative algebra -/

/-- Ring-theoretic core of the split-versus-unsplit defect.  The three
denominators are represented only through the inverse laws used by the
calculation. -/
theorem cayley_split_defect_core {R₀ : Type*} [Ring R₀]
    (X Y RX RY RXY : R₀)
    (hXR : (1 + X) * RX = 1)
    (hYR : (1 + Y) * RY = 1)
    (hXYR : (1 + (X + Y)) * RXY = 1)
    (hRXY : RXY * (1 + (X + Y)) = 1) :
    ((1 - X) * RX) * ((1 - Y) * RY) - (1 - (X + Y)) * RXY =
      (2 : R₀) *
        (X * RX * Y * RY - RXY * Y * X * RX * RY) := by
  have hXRX : X * RX = 1 - RX := by
    calc
      X * RX = (1 + X) * RX - RX := by noncomm_ring
      _ = 1 - RX := by rw [hXR]
  have hYRY : Y * RY = 1 - RY := by
    calc
      Y * RY = (1 + Y) * RY - RY := by noncomm_ring
      _ = 1 - RY := by rw [hYR]
  have hQuadratic :
      X * RX * Y * RY = 1 - RX - RY + RX * RY := by
    calc
      X * RX * Y * RY = (X * RX) * (Y * RY) := by noncomm_ring
      _ = (1 - RX) * (1 - RY) := by rw [hXRX, hYRY]
      _ = 1 - RX - RY + RX * RY := by noncomm_ring
  have hDenominatorExpansion :
      (1 + (X + Y)) * RX * RY + Y * X * RX * RY = 1 := by
    calc
      (1 + (X + Y)) * RX * RY + Y * X * RX * RY =
          ((1 + X) * RX) * RY + Y * ((1 + X) * RX) * RY := by
            noncomm_ring
      _ = RY + Y * RY := by rw [hXR]; simp
      _ = (1 + Y) * RY := by noncomm_ring
      _ = 1 := hYR
  have hYX :
      Y * X * RX * RY = 1 - (1 + (X + Y)) * RX * RY := by
    calc
      Y * X * RX * RY =
          ((1 + (X + Y)) * RX * RY + Y * X * RX * RY) -
            (1 + (X + Y)) * RX * RY := by
              noncomm_ring
      _ = 1 - (1 + (X + Y)) * RX * RY := by
        rw [hDenominatorExpansion]
  have hResolventQuadratic :
      RXY * Y * X * RX * RY = RXY - RX * RY := by
    calc
      RXY * Y * X * RX * RY = RXY * (Y * X * RX * RY) := by
        noncomm_ring
      _ = RXY * (1 - (1 + (X + Y)) * RX * RY) := by rw [hYX]
      _ = RXY - (RXY * (1 + (X + Y))) * RX * RY := by
        noncomm_ring
      _ = RXY - RX * RY := by rw [hRXY]; simp
  rw [cayley_affine_of_right_inverse X RX hXR,
    cayley_affine_of_right_inverse Y RY hYR,
    cayley_affine_of_right_inverse (X + Y) RXY hXYR]
  rw [hQuadratic, hResolventQuadratic]
  noncomm_ring

private theorem matrix_two_mul {n : ℕ} (Z : Mat n) :
    (2 : Mat n) * Z = (2 : ℂ) • Z := by
  calc
    (2 : Mat n) * Z = 2 • Z := (nsmul_eq_mul 2 Z).symm
    _ = (2 : ℂ) • Z := (Nat.cast_smul_eq_nsmul ℂ 2 Z).symm

private theorem skewPart_split_quadratic {n : ℕ}
    (X Y RX RY RXY : Mat n) (alpha : ℝ) :
    skewPart alpha X * RX * skewPart alpha Y * RY -
        RXY * skewPart alpha Y * skewPart alpha X * RX * RY =
      ((alpha : ℂ) ^ 2) •
        (RXY * Y * X * RX * RY - X * RX * Y * RY) := by
  have hcscalar_sq :
      (Complex.I * (alpha : ℂ)) * (Complex.I * (alpha : ℂ)) =
        -((alpha : ℂ) ^ 2) := by
    calc
      (Complex.I * (alpha : ℂ)) * (Complex.I * (alpha : ℂ)) =
          (Complex.I * Complex.I) * ((alpha : ℂ) * (alpha : ℂ)) := by
            ring
      _ = -((alpha : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
  have hFirst :
      skewPart alpha X * RX * skewPart alpha Y * RY =
        (-((alpha : ℂ) ^ 2)) • (X * RX * Y * RY) := by
    simp only [skewPart, cscalar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcscalar_sq]
  have hSecond :
      RXY * skewPart alpha Y * skewPart alpha X * RX * RY =
        (-((alpha : ℂ) ^ 2)) • (RXY * Y * X * RX * RY) := by
    simp only [skewPart, cscalar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcscalar_sq]
  rw [hFirst, hSecond]
  module

/-! ## Exact matrix identity -/

/-- Exact split-versus-unsplit Cayley defect for arbitrary finite Hermitian
complex matrices and every real step, including zero and negative steps. -/
theorem cayley_split_unsplit_defect {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cayley alpha A * cayley alpha B - cayley alpha (A + B) =
      (2 * (alpha : ℂ) ^ 2) •
        (cayleyR alpha (A + B) * B * A * cayleyR alpha A * cayleyR alpha B -
          A * cayleyR alpha A * B * cayleyR alpha B) := by
  have hAB : (A + B).IsHermitian := hA.add hB
  have hSkewAdd :
      skewPart alpha (A + B) = skewPart alpha A + skewPart alpha B := by
    simp only [skewPart, smul_add]
  have hDAR :
      (1 + skewPart alpha A) * cayleyR alpha A = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha A hA
  have hDBR :
      (1 + skewPart alpha B) * cayleyR alpha B = 1 := by
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha B hB
  have hDABR :
      (1 + (skewPart alpha A + skewPart alpha B)) *
          cayleyR alpha (A + B) = 1 := by
    rw [← hSkewAdd]
    simpa only [cayleyD] using cayleyD_mul_cayleyR alpha (A + B) hAB
  have hRABD :
      cayleyR alpha (A + B) *
          (1 + (skewPart alpha A + skewPart alpha B)) = 1 := by
    rw [← hSkewAdd]
    simpa only [cayleyD] using cayleyR_mul_cayleyD alpha (A + B) hAB
  change
    ((1 - skewPart alpha A) * cayleyR alpha A) *
          ((1 - skewPart alpha B) * cayleyR alpha B) -
        (1 - skewPart alpha (A + B)) * cayleyR alpha (A + B) = _
  rw [hSkewAdd]
  calc
    ((1 - skewPart alpha A) * cayleyR alpha A) *
          ((1 - skewPart alpha B) * cayleyR alpha B) -
        (1 - (skewPart alpha A + skewPart alpha B)) *
          cayleyR alpha (A + B) =
        (2 : Mat n) *
          (skewPart alpha A * cayleyR alpha A *
                skewPart alpha B * cayleyR alpha B -
            cayleyR alpha (A + B) * skewPart alpha B *
              skewPart alpha A * cayleyR alpha A * cayleyR alpha B) :=
      cayley_split_defect_core
        (skewPart alpha A) (skewPart alpha B)
        (cayleyR alpha A) (cayleyR alpha B) (cayleyR alpha (A + B))
        hDAR hDBR hDABR hRABD
    _ = (2 * (alpha : ℂ) ^ 2) •
        (cayleyR alpha (A + B) * B * A * cayleyR alpha A *
              cayleyR alpha B -
          A * cayleyR alpha A * B * cayleyR alpha B) := by
      rw [skewPart_split_quadratic, matrix_two_mul, smul_smul]

/-! ## Continuous-linear-map transport and induced operator norm -/

private theorem cayley_split_unsplit_defect_CLM {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Chat A alpha * Chat B alpha - Chat (A + B) alpha =
      (2 * (alpha : ℂ) ^ 2) •
        (Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
              Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha) := by
  simpa only [map_mul, map_sub, map_smul] using
    congrArg
      (fun M : Mat n =>
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayley_split_unsplit_defect alpha A B hA hB)

/-- The exact local splitting defect is quadratically bounded in the real
step in the induced operator norm on the standard complex Euclidean space. -/
theorem cayley_split_unsplit_defect_opNorm_le {n : ℕ}
    (alpha : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Chat A alpha * Chat B alpha - Chat (A + B) alpha‖ ≤
      4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
  have hAB : (A + B).IsHermitian := hA.add hB
  have hRA : ‖Rhat A alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha A hA
  have hRB : ‖Rhat B alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha B hB
  have hRAB : ‖Rhat (A + B) alpha‖ ≤ 1 :=
    cayleyR_toEuclideanCLM_opNorm_le_one alpha (A + B) hAB
  have hFirst :
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
          Rhat B alpha‖ ≤ ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
          Rhat B alpha‖ ≤
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha‖ *
            ‖Rhat B alpha‖ := norm_mul_le _ _
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A *
            Rhat A alpha‖ := by
        simpa using mul_le_mul_of_nonneg_left hRB (norm_nonneg _)
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A‖ *
            ‖Rhat A alpha‖ := norm_mul_le _ _
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B * operatorOf A‖ := by
        simpa using mul_le_mul_of_nonneg_left hRA (norm_nonneg _)
      _ ≤ ‖Rhat (A + B) alpha * operatorOf B‖ * ‖operatorOf A‖ :=
        norm_mul_le _ _
      _ ≤ (‖Rhat (A + B) alpha‖ * ‖operatorOf B‖) *
            ‖operatorOf A‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * ‖operatorOf B‖) * ‖operatorOf A‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hRAB (norm_nonneg _)) (norm_nonneg _)
      _ = ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  have hSecond :
      ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
          ‖operatorOf A * Rhat A alpha * operatorOf B‖ *
            ‖Rhat B alpha‖ := norm_mul_le _ _
      _ ≤ ‖operatorOf A * Rhat A alpha * operatorOf B‖ := by
        simpa using mul_le_mul_of_nonneg_left hRB (norm_nonneg _)
      _ ≤ ‖operatorOf A * Rhat A alpha‖ * ‖operatorOf B‖ :=
        norm_mul_le _ _
      _ ≤ (‖operatorOf A‖ * ‖Rhat A alpha‖) * ‖operatorOf B‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖operatorOf A‖ * 1) * ‖operatorOf B‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRA (norm_nonneg _)) (norm_nonneg _)
      _ = ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  have hInside :
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
            Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by
    calc
      ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
            Rhat B alpha -
          operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
              Rhat B alpha‖ +
            ‖operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ :=
        norm_sub_le _ _
      _ ≤ ‖operatorOf A‖ * ‖operatorOf B‖ +
            ‖operatorOf A‖ * ‖operatorOf B‖ := add_le_add hFirst hSecond
      _ = 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by ring
  rw [cayley_split_unsplit_defect_CLM alpha A B hA hB, norm_smul]
  have hScalar :
      ‖(2 : ℂ) * (alpha : ℂ) ^ 2‖ = 2 * alpha ^ 2 := by
    simp only [norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hScalar]
  calc
    2 * alpha ^ 2 *
          ‖Rhat (A + B) alpha * operatorOf B * operatorOf A * Rhat A alpha *
                Rhat B alpha -
            operatorOf A * Rhat A alpha * operatorOf B * Rhat B alpha‖ ≤
        2 * alpha ^ 2 * (2 * ‖operatorOf A‖ * ‖operatorOf B‖) :=
      mul_le_mul_of_nonneg_left hInside
        (mul_nonneg (by norm_num) (sq_nonneg alpha))
    _ = 4 * alpha ^ 2 * ‖operatorOf A‖ * ‖operatorOf B‖ := by ring

end NDEAEvolve.Exp003

#check @NDEAEvolve.Exp003.cayley_split_defect_core
#check @NDEAEvolve.Exp003.cayley_split_unsplit_defect
#check @NDEAEvolve.Exp003.cayley_split_unsplit_defect_opNorm_le
#print axioms NDEAEvolve.Exp003.cayley_split_unsplit_defect
#print axioms NDEAEvolve.Exp003.cayley_split_unsplit_defect_opNorm_le
