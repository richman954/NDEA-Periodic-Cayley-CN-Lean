import NDEAMathlibGate.TemporalTaylorRemainderBoundsV1
import NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1

/-! Analytic discharge of the Crank--Nicolson local Taylor premises. -/

noncomputable section

open Complex Set

namespace NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1

open NDEAMathlibGate.TemporalTaylorRemainderBoundsV1
open NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1

theorem quadraticRemainder_eq_stateTaylorRemainder
    (u : ℝ → ℂ) (t k : ℝ) :
    quadraticRemainder u t k =
      stateTaylorRemainder (u t) (u (t + k))
        (iteratedDeriv 1 u t) (iteratedDeriv 2 u t) k := by
  simp [quadraticRemainder, quadraticTaylor, stateTaylorRemainder,
    Complex.real_smul]
  ring

theorem linearRemainder_eq_derivTaylorRemainder
    (du : ℝ → ℂ) (t k : ℝ) :
    linearRemainder du t k =
      derivTaylorRemainder (du t) (du (t + k))
        (iteratedDeriv 1 du t) k := by
  simp [linearRemainder, linearTaylor, derivTaylorRemainder,
    Complex.real_smul]
  ring

theorem cnFunctionLocalDefect_norm_bound_of_contDiff
    (u du : ℝ → ℂ) (t k M : ℝ) (hk : 0 < k)
    (hu : ContDiff ℝ 3 u) (hdu : ContDiff ℝ 2 du)
    (hdu0 : du t = iteratedDeriv 1 u t)
    (hdu1 : du (t + k) = iteratedDeriv 1 u (t + k))
    (hd2 : iteratedDeriv 1 du t = iteratedDeriv 2 u t)
    (hu3 : ∀ x ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 3 u (Set.Icc t (t + k)) x‖ ≤ M)
    (hdu2 : ∀ x ∈ Set.Icc t (t + k),
      ‖iteratedDerivWithin 2 du (Set.Icc t (t + k)) x‖ ≤ M) :
    ‖cnFunctionLocalDefect u t k‖ ≤ 5 * M * k ^ 2 / 12 := by
  have hs := quadraticRemainder_norm_bound u t k M hk hu hu3
  rw [quadraticRemainder_eq_stateTaylorRemainder] at hs
  have hd := linearRemainder_norm_bound du t k M hk hdu hdu2
  rw [linearRemainder_eq_derivTaylorRemainder] at hd
  rw [hdu0, hdu1, hd2] at hd
  exact cnFunctionLocalDefect_norm_bound u t k M hk hs hd

def temporalConsistencyStatus : String :=
  "analytic_crank_nicolson_local_temporal_consistency_validated"

theorem temporalConsistencyStatus_true :
    temporalConsistencyStatus =
      "analytic_crank_nicolson_local_temporal_consistency_validated" := rfl

end NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1
