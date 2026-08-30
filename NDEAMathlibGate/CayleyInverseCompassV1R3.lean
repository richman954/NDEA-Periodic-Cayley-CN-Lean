import Mathlib
import NDEAMathlibGate.CayleyDeterminantCompassV2R

namespace NDEAMathlibGate
namespace CayleyInverseCompassV1R3

/-!
Cayley Inverse Compass V1R3

Finite exact rational-complex pair model.
This proves a concrete 2x2 inverse and unitarity-style compass.

Scope:
  finite 2x2 compass only;
  no general operator theorem;
  no continuous PDE claim.
-/

structure C2 where
  re : Rat
  im : Rat
deriving Repr, DecidableEq

def c0 : C2 := { re := 0, im := 0 }
def c1 : C2 := { re := 1, im := 0 }
def ci : C2 := { re := 0, im := 1 }
def cni : C2 := { re := 0, im := -1 }
def chalf : C2 := { re := (1 : Rat) / 2, im := 0 }
def cihalf : C2 := { re := 0, im := (1 : Rat) / 2 }
def cnihalf : C2 := { re := 0, im := -((1 : Rat) / 2) }

def cadd (z w : C2) : C2 :=
  { re := z.re + w.re, im := z.im + w.im }

def cneg (z : C2) : C2 :=
  { re := -z.re, im := -z.im }

def csub (z w : C2) : C2 :=
  cadd z (cneg w)

def cmul (z w : C2) : C2 :=
  { re := z.re * w.re - z.im * w.im,
    im := z.re * w.im + z.im * w.re }

def cconj (z : C2) : C2 :=
  { re := z.re, im := -z.im }

theorem ci_mul_ci :
    cmul ci ci = { re := -1, im := 0 } := by
  native_decide

abbrev MatrixState := Matrix (Fin 2) (Fin 2) C2

def matmul2 (A B : MatrixState) : MatrixState :=
  !![ cadd (cmul (A 0 0) (B 0 0)) (cmul (A 0 1) (B 1 0)),
      cadd (cmul (A 0 0) (B 0 1)) (cmul (A 0 1) (B 1 1));
      cadd (cmul (A 1 0) (B 0 0)) (cmul (A 1 1) (B 1 0)),
      cadd (cmul (A 1 0) (B 0 1)) (cmul (A 1 1) (B 1 1)) ]

def trace2 (A : MatrixState) : C2 :=
  cadd (A 0 0) (A 1 1)

def det2 (A : MatrixState) : C2 :=
  csub (cmul (A 0 0) (A 1 1)) (cmul (A 0 1) (A 1 0))

def adjoint2 (A : MatrixState) : MatrixState :=
  !![ cconj (A 0 0), cconj (A 1 0);
      cconj (A 0 1), cconj (A 1 1) ]

def id_matrix : MatrixState :=
  !![c1, c0; c0, c1]

def zero_matrix : MatrixState :=
  !![c0, c0; c0, c0]

/-- Concrete Hermitian sample H = [[0,1],[1,0]]. -/
def H_sample : MatrixState :=
  !![c0, c1; c1, c0]

/-- L = I + iH for alpha = 1. -/
def L : MatrixState :=
  !![c1, ci; ci, c1]

/-- R = I - iH for alpha = 1. -/
def R : MatrixState :=
  !![c1, cni; cni, c1]

/-- Correct inverse of L. -/
def L_inv : MatrixState :=
  !![chalf, cnihalf; cnihalf, chalf]

theorem L_left_inverse :
    matmul2 L_inv L = id_matrix := by
  native_decide

theorem L_right_inverse :
    matmul2 L L_inv = id_matrix := by
  native_decide

theorem det2_L :
    det2 L = { re := 2, im := 0 } := by
  native_decide

theorem det2_L_nonzero :
    det2 L ≠ c0 := by
  native_decide

/-- Finite Cayley transform U = R * L_inv. -/
def U : MatrixState :=
  matmul2 R L_inv

def U_expected : MatrixState :=
  !![c0, cni; cni, c0]

theorem U_formula :
    U = U_expected := by
  native_decide

def U_adj : MatrixState :=
  adjoint2 U_expected

def U_adj_expected : MatrixState :=
  !![c0, ci; ci, c0]

theorem U_adj_formula :
    U_adj = U_adj_expected := by
  native_decide

theorem U_unitary_left :
    matmul2 U_adj U = id_matrix := by
  native_decide

theorem U_unitary_right :
    matmul2 U U_adj = id_matrix := by
  native_decide

/-- The V6R stress-boundary matrix is singular and kept separate from L. -/
def V6R_stress_boundary : MatrixState :=
  !![c1, ci; cni, c1]

theorem det2_V6R_stress_boundary_zero :
    det2 V6R_stress_boundary = c0 := by
  native_decide

theorem fake_inverse_does_not_invert_V6R_stress_boundary :
    matmul2 id_matrix V6R_stress_boundary ≠ id_matrix := by
  native_decide

def continuousPDEFormalizationStatusCayleyInverseV1R3 : String :=
  "not_claimed"

def cayleyInverseCompassStatusV1R3 : String :=
  "finite_2x2_exact_pair_inverse_and_unitarity_compass_only"

theorem true_continuousPDE_status_not_claimed :
    continuousPDEFormalizationStatusCayleyInverseV1R3 = "not_claimed" := by
  rfl

theorem true_cayley_inverse_compass_status :
    cayleyInverseCompassStatusV1R3 =
      "finite_2x2_exact_pair_inverse_and_unitarity_compass_only" := by
  rfl

#check L_left_inverse
#check L_right_inverse
#check U_unitary_left
#check U_unitary_right
#check fake_inverse_does_not_invert_V6R_stress_boundary

end CayleyInverseCompassV1R3
end NDEAMathlibGate
