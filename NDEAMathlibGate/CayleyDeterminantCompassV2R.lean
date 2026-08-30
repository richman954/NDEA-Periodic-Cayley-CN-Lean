import Mathlib

open Matrix

namespace NDEAMathlibGate
namespace CayleyDeterminantCompassV2R

/-!
Cayley Determinant Compass V2R

Repair of V2:
  - Accepts lakefile.toml or lakefile.lean at preflight.
  - Keeps the compass finite and exact.
  - Uses Mathlib for Complex.I and Matrix.det smoke checks.
  - Uses an exact Rat-pair complex model for robust determinant formulas.

Scope:
  - finite 2x2 determinant algebra only;
  - no inverse construction;
  - no unitarity theorem;
  - no PML/operator theorem;
  - no continuous PDE theorem.
-/

/-- Gate theorem: Mathlib knows I * I = -1. -/
theorem complex_I_mul_I_gate :
    Complex.I * Complex.I = -1 := by
  simpa using Complex.I_mul_I

/-- Matrix.det smoke test over Rat, matching the Mathlib Gate result. -/
def M2Rat : Matrix (Fin 2) (Fin 2) Rat :=
  !![1, 2; 3, 4]

theorem matrix_det_M2_eq_neg_two :
    M2Rat.det = -2 := by
  native_decide

/-- A tiny exact complex-number type over Rat for deterministic compass algebra. -/
structure C2 where
  re : Rat
  im : Rat
deriving Repr, DecidableEq

def c2zero : C2 := { re := 0, im := 0 }
def c2one : C2 := { re := 1, im := 0 }
def c2I : C2 := { re := 0, im := 1 }
def c2negOne : C2 := { re := -1, im := 0 }

def c2add (z w : C2) : C2 :=
  { re := z.re + w.re, im := z.im + w.im }

def c2neg (z : C2) : C2 :=
  { re := -z.re, im := -z.im }

def c2sub (z w : C2) : C2 :=
  c2add z (c2neg w)

def c2mul (z w : C2) : C2 :=
  { re := z.re * w.re - z.im * w.im,
    im := z.re * w.im + z.im * w.re }

theorem c2_I_mul_I_eq_neg_one :
    c2mul c2I c2I = c2negOne := by
  native_decide

def alphaRat : Rat := (1 : Rat) / 10

/-- L = I + i α H for diagonal H = diag(1,2), represented exactly over rational complex pairs. -/
def L00 : C2 := { re := 1, im := alphaRat }
def L01 : C2 := c2zero
def L10 : C2 := c2zero
def L11 : C2 := { re := 1, im := 2 * alphaRat }

/-- R = I - i α H for the same H. -/
def R00 : C2 := { re := 1, im := -alphaRat }
def R01 : C2 := c2zero
def R10 : C2 := c2zero
def R11 : C2 := { re := 1, im := -(2 * alphaRat) }

def det2C2 (a00 a01 a10 a11 : C2) : C2 :=
  c2sub (c2mul a00 a11) (c2mul a01 a10)

def cayleyLeftDetC2 : C2 :=
  det2C2 L00 L01 L10 L11

def cayleyRightDetC2 : C2 :=
  det2C2 R00 R01 R10 R11

def cayleyLeftExpectedC2 : C2 :=
  { re := (49 : Rat) / 50, im := (3 : Rat) / 10 }

def cayleyRightExpectedC2 : C2 :=
  { re := (49 : Rat) / 50, im := -(3 : Rat) / 10 }

theorem cayley_left_det_c2_formula :
    cayleyLeftDetC2 = cayleyLeftExpectedC2 := by
  native_decide

theorem cayley_right_det_c2_formula :
    cayleyRightDetC2 = cayleyRightExpectedC2 := by
  native_decide

/-- Determinant is nonzero in the exact rational-complex model. -/
theorem cayley_left_det_c2_nonzero :
    cayleyLeftDetC2 ≠ c2zero := by
  native_decide

theorem cayley_right_det_c2_nonzero :
    cayleyRightDetC2 ≠ c2zero := by
  native_decide

/-- Boundary marker: this is not a PDE formalization. -/
def continuousPDEFormalizationStatusCayleyV2R : String :=
  "not_claimed"

/-- Boundary marker: this is a finite determinant compass, not full Cayley unitarity. -/
def cayleyCompassStatusV2R : String :=
  "finite_2x2_determinant_compass_only"

theorem true_continuousPDE_status_cayley_v2r_not_claimed :
    continuousPDEFormalizationStatusCayleyV2R = "not_claimed" := by
  rfl

theorem true_cayley_compass_status_v2r :
    cayleyCompassStatusV2R = "finite_2x2_determinant_compass_only" := by
  rfl

#eval M2Rat.det
#eval cayleyLeftDetC2
#eval cayleyRightDetC2
#eval continuousPDEFormalizationStatusCayleyV2R
#eval cayleyCompassStatusV2R

end CayleyDeterminantCompassV2R
end NDEAMathlibGate
