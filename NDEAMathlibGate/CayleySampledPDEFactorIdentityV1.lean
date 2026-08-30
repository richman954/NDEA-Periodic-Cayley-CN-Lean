import NDEAMathlibGate.CayleyResidualRecurrenceIdentityV1

/-! Convert the semidiscrete Schrodinger equation into a Cayley factor residual. -/

noncomputable section

namespace NDEAMathlibGate.CayleySampledPDEFactorIdentityV1

open Matrix Complex
open NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Vec (n : ℕ) := Fin n → ℂ

def cnResidualVector {n : ℕ}
    (uNow uNext duNow duNext : Vec n) (k : ℝ) : Vec n :=
  fun i => (uNext i - uNow i) / (k : ℂ) - (duNext i + duNow i) / 2

def combinedFactorResidualVector {n : ℕ}
    (H : Mat n) (uNow uNext duNow duNext : Vec n) (k : ℝ) : Vec n :=
  fun i =>
    cnResidualVector uNow uNext duNow duNext k i +
      (duNext i + duNow i) / 2 +
      Complex.I / 2 * (H.mulVec (uNext + uNow)) i

def spatialMismatchVector {n : ℕ}
    (H : Mat n) (uNow uNext dxxAverage : Vec n) : Vec n :=
  H.mulVec ((2 : ℂ)⁻¹ • (uNext + uNow)) + dxxAverage

def rotatedSpaceTimeResidualVector {n : ℕ}
    (H : Mat n) (uNow uNext duNow duNext dxxAverage : Vec n) (k : ℝ) : Vec n :=
  cnResidualVector uNow uNext duNow duNext k +
    Complex.I • spatialMismatchVector H uNow uNext dxxAverage

theorem combined_factor_residual_eq_rotated_space_time {n : ℕ}
    (H : Mat n) (uNow uNext duNow duNext dxxAverage : Vec n) (k : ℝ)
    (hPDEAverage : (2 : ℂ)⁻¹ • (duNext + duNow) =
      Complex.I • dxxAverage) :
    combinedFactorResidualVector H uNow uNext duNow duNext k =
      rotatedSpaceTimeResidualVector H uNow uNext duNow duNext dxxAverage k := by
  ext i
  have hi := congrFun hPDEAverage i
  simp [combinedFactorResidualVector, rotatedSpaceTimeResidualVector,
    spatialMismatchVector, Matrix.mulVec_add, Matrix.mulVec_smul] at hi ⊢
  have hi' : (duNext i + duNow i) / 2 = Complex.I * dxxAverage i := by
    calc
      (duNext i + duNow i) / 2 = (2 : ℂ)⁻¹ * (duNext i + duNow i) := by ring
      _ = Complex.I * dxxAverage i := hi
  rw [hi']
  ring

theorem general_derivative_to_factor_residual {n : ℕ}
    (k : ℝ) (hk : k ≠ 0) (H : Mat n)
    (uNow uNext duNow duNext : Vec n) :
    (cayleyA (k / 2) H).mulVec uNext =
      (cayleyB (k / 2) H).mulVec uNow +
        k • combinedFactorResidualVector H uNow uNext duNow duNext k := by
  ext i
  simp [cayleyA, cayleyB, cscalar, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    combinedFactorResidualVector, cnResidualVector]
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  field_simp [hkC]
  ring

theorem semidiscrete_schrodinger_to_factor_residual {n : ℕ}
    (k : ℝ) (hk : k ≠ 0) (H : Mat n)
    (uNow uNext duNow duNext : Vec n)
    (hduNow : duNow = (-Complex.I) • H.mulVec uNow)
    (hduNext : duNext = (-Complex.I) • H.mulVec uNext) :
    (cayleyA (k / 2) H).mulVec uNext =
      (cayleyB (k / 2) H).mulVec uNow +
        k • cnResidualVector uNow uNext duNow duNext k := by
  ext i
  have hduNowI := congrFun hduNow i
  have hduNextI := congrFun hduNext i
  simp [cayleyA, cayleyB, cscalar, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, cnResidualVector] at hduNowI hduNextI ⊢
  rw [hduNowI, hduNextI]
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  field_simp [hkC]
  ring_nf

def sampledPDEFactorIdentityStatus : String :=
  "semidiscrete_schrodinger_cn_residual_equals_cayley_factor_residual"

end NDEAMathlibGate.CayleySampledPDEFactorIdentityV1
