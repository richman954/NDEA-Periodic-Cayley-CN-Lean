import NDEAMathlibGate.CayleyCrankNicolsonIdentityV1

/-!
Quantitative local temporal consistency for the Crank--Nicolson residual.

This module isolates the exact Taylor-remainder assembly.  If the state and
its first derivative have the standard third- and second-order Taylor
remainder bounds, respectively, the normalized Crank--Nicolson defect is
second order in the time step.
-/

noncomputable section

open Complex

namespace NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1

def cnLocalDefect
    (u0 u1 du0 du1 : ℂ) (k : ℝ) : ℂ :=
  (u1 - u0) / (k : ℂ) - (du1 + du0) / 2

def stateTaylorRemainder
    (u0 u1 du0 d2u0 : ℂ) (k : ℝ) : ℂ :=
  u1 - u0 - (k : ℂ) * du0 - (k : ℂ) ^ 2 / 2 * d2u0

def derivTaylorRemainder
    (du0 du1 d2u0 : ℂ) (k : ℝ) : ℂ :=
  du1 - du0 - (k : ℂ) * d2u0

theorem cnLocalDefect_eq_taylorRemainders
    (u0 u1 du0 du1 d2u0 : ℂ) (k : ℝ) (hk : k ≠ 0) :
    cnLocalDefect u0 u1 du0 du1 k =
      stateTaylorRemainder u0 u1 du0 d2u0 k / (k : ℂ) -
        derivTaylorRemainder du0 du1 d2u0 k / 2 := by
  simp only [cnLocalDefect, stateTaylorRemainder, derivTaylorRemainder]
  have hkC : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  field_simp [hkC]
  ring

theorem cnLocalDefect_norm_bound
    (u0 u1 du0 du1 d2u0 : ℂ) (k M : ℝ)
    (hk : 0 < k)
    (hstate : ‖stateTaylorRemainder u0 u1 du0 d2u0 k‖ ≤ M * k ^ 3 / 6)
    (hderiv : ‖derivTaylorRemainder du0 du1 d2u0 k‖ ≤ M * k ^ 2 / 2) :
    ‖cnLocalDefect u0 u1 du0 du1 k‖ ≤ 5 * M * k ^ 2 / 12 := by
  rw [cnLocalDefect_eq_taylorRemainders u0 u1 du0 du1 d2u0 k hk.ne']
  calc
    ‖stateTaylorRemainder u0 u1 du0 d2u0 k / (k : ℂ) -
        derivTaylorRemainder du0 du1 d2u0 k / 2‖ ≤
        ‖stateTaylorRemainder u0 u1 du0 d2u0 k / (k : ℂ)‖ +
          ‖derivTaylorRemainder du0 du1 d2u0 k / 2‖ := norm_sub_le _ _
    _ = ‖stateTaylorRemainder u0 u1 du0 d2u0 k‖ / k +
          ‖derivTaylorRemainder du0 du1 d2u0 k‖ / 2 := by
      rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk]
      norm_num
    _ ≤ (M * k ^ 3 / 6) / k + (M * k ^ 2 / 2) / 2 := by
      exact add_le_add
        (div_le_div_of_nonneg_right hstate hk.le)
        (div_le_div_of_nonneg_right hderiv (by norm_num))
    _ = 5 * M * k ^ 2 / 12 := by
      field_simp [hk.ne']
      ring

theorem cnLocalDefect_unnormalized_norm_bound
    (u0 u1 du0 du1 d2u0 : ℂ) (k M : ℝ)
    (hk : 0 < k)
    (hstate : ‖stateTaylorRemainder u0 u1 du0 d2u0 k‖ ≤ M * k ^ 3 / 6)
    (hderiv : ‖derivTaylorRemainder du0 du1 d2u0 k‖ ≤ M * k ^ 2 / 2) :
    ‖(k : ℂ) * cnLocalDefect u0 u1 du0 du1 k‖ ≤
      5 * M * k ^ 3 / 12 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    k * ‖cnLocalDefect u0 u1 du0 du1 k‖ ≤
        k * (5 * M * k ^ 2 / 12) :=
      mul_le_mul_of_nonneg_left
        (cnLocalDefect_norm_bound u0 u1 du0 du1 d2u0 k M hk hstate hderiv)
        hk.le
    _ = 5 * M * k ^ 3 / 12 := by ring

def cnFunctionLocalDefect (u : ℝ → ℂ) (t k : ℝ) : ℂ :=
  cnLocalDefect (u t) (u (t + k))
    (iteratedDeriv 1 u t) (iteratedDeriv 1 u (t + k)) k

theorem cnFunctionLocalDefect_norm_bound
    (u : ℝ → ℂ) (t k M : ℝ) (hk : 0 < k)
    (hstate :
      ‖stateTaylorRemainder (u t) (u (t + k))
          (iteratedDeriv 1 u t) (iteratedDeriv 2 u t) k‖ ≤
        M * k ^ 3 / 6)
    (hderiv :
      ‖derivTaylorRemainder (iteratedDeriv 1 u t)
          (iteratedDeriv 1 u (t + k)) (iteratedDeriv 2 u t) k‖ ≤
        M * k ^ 2 / 2) :
    ‖cnFunctionLocalDefect u t k‖ ≤ 5 * M * k ^ 2 / 12 := by
  exact cnLocalDefect_norm_bound
    (u t) (u (t + k)) (iteratedDeriv 1 u t)
    (iteratedDeriv 1 u (t + k)) (iteratedDeriv 2 u t)
    k M hk hstate hderiv

def localTruncationStatus : String :=
  "crank_nicolson_local_defect_second_order_from_taylor_remainders_validated"

theorem localTruncationStatus_true :
    localTruncationStatus =
      "crank_nicolson_local_defect_second_order_from_taylor_remainders_validated" := rfl

end NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1
