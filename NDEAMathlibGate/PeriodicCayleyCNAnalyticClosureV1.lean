import NDEAMathlibGate.PeriodicCayleyCrankNicolsonConvergenceV1
import NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1

/-! Discharge the analytic premises of periodic Cayley/CN convergence from a
single smooth periodic space--time field. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1

open Complex Set
open NDEAMathlibGate.CayleyCrankNicolsonLocalTruncationV1
open NDEAMathlibGate.CayleyCrankNicolsonTemporalConsistencyV1
open NDEAMathlibGate.CayleySampledPDEFactorIdentityV1
open NDEAMathlibGate.CayleyEuclideanIsometryV1
open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicSampledFactorResidualDecompositionV1
open NDEAMathlibGate.PeriodicCayleyCrankNicolsonConvergenceV1

def timeProfile (U : ℝ → ℝ → ℂ) (x : ℝ) : ℝ → ℂ :=
  fun t => U t x

def stepProfile (U : ℝ → ℝ → ℂ) (k : ℝ) (j : ℕ) : ℝ → ℂ :=
  U ((j : ℝ) * k)

def sampledTimeDerivative
    (U : ℝ → ℝ → ℂ) (L k : ℝ) (m : ℕ) (j : ℕ) : Fin (m + 1) → ℂ :=
  fun i => iteratedDeriv 1 (timeProfile U (gridPoint L (m + 1) i)) ((j : ℝ) * k)

theorem iteratedDerivWithin_Icc_eq_iteratedDeriv
    (f : ℝ → ℂ) (n : ℕ) (t k x : ℝ) (hk : 0 < k)
    (hf : ContDiff ℝ n f) (hx : x ∈ Icc t (t + k)) :
    iteratedDerivWithin n f (Icc t (t + k)) x = iteratedDeriv n f x := by
  exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
    hf.contDiffAt hx

theorem sampledCNTemporalResidual_norm_bound_of_uniform_time_regular
    (U : ℝ → ℝ → ℂ) (L k Mt : ℝ) (m : ℕ) (hk : 0 < k)
    (hTimeC3 : ∀ x, ContDiff ℝ 3 (timeProfile U x))
    (hTime3 : ∀ x t, ‖iteratedDeriv 3 (timeProfile U x) t‖ ≤ Mt) :
    ∀ j i,
      ‖sampledCNTemporalResidual L k m (stepProfile U k)
          (sampledTimeDerivative U L k m) j i‖ ≤ 5 * Mt * k ^ 2 / 12 := by
  intro j i
  let x := gridPoint L (m + 1) i
  let t := (j : ℝ) * k
  let u := timeProfile U x
  have hdu : ContDiff ℝ 2 (iteratedDeriv 1 u) := by
    rw [show iteratedDeriv 1 u = deriv u by simp [iteratedDeriv_succ]]
    exact (hTimeC3 x).deriv'
  have hlocal := cnFunctionLocalDefect_norm_bound_of_contDiff
    u (iteratedDeriv 1 u) t k Mt hk (hTimeC3 x) hdu
    rfl rfl (by simp [iteratedDeriv_succ])
    (fun y hy => by
      rw [iteratedDerivWithin_Icc_eq_iteratedDeriv u 3 t k y hk (hTimeC3 x) hy]
      exact hTime3 x y)
    (fun y hy => by
      rw [iteratedDerivWithin_Icc_eq_iteratedDeriv
        (iteratedDeriv 1 u) 2 t k y hk hdu hy]
      simpa [iteratedDeriv_succ] using hTime3 x y)
  simpa [sampledCNTemporalResidual, sampledTimeDerivative, stepProfile,
    sampleFixedPeriod, cnResidualVector, cnFunctionLocalDefect, cnLocalDefect,
    u, t, x, timeProfile, Nat.cast_add, Nat.cast_one, add_mul] using hlocal

theorem averageProfile_periodic
    (uNow uNext : ℝ → ℂ) (L : ℝ)
    (hNow : Function.Periodic uNow L) (hNext : Function.Periodic uNext L) :
    Function.Periodic (averageProfile uNow uNext) L := by
  intro x
  simp only [averageProfile]
  rw [hNext x, hNow x]

theorem averageProfile_contDiff_four
    (uNow uNext : ℝ → ℂ)
    (hNow : ContDiff ℝ 4 uNow) (hNext : ContDiff ℝ 4 uNext) :
    ContDiff ℝ 4 (averageProfile uNow uNext) := by
  have havg : averageProfile uNow uNext = (2 : ℂ)⁻¹ • (uNext + uNow) := by
    funext y
    simp [averageProfile, div_eq_mul_inv, mul_comm]
  rw [havg]
  have h := ContDiff.const_smul (2 : ℂ)⁻¹ (hNext.add hNow)
  exact h

theorem iteratedDeriv_averageProfile
    (n : ℕ) (uNow uNext : ℝ → ℂ) (x : ℝ)
    (hNow : ContDiff ℝ n uNow) (hNext : ContDiff ℝ n uNext) :
    iteratedDeriv n (averageProfile uNow uNext) x =
      (2 : ℂ)⁻¹ • (iteratedDeriv n uNext x + iteratedDeriv n uNow x) := by
  have havg : averageProfile uNow uNext = (2 : ℂ)⁻¹ • (uNext + uNow) := by
    funext y
    simp [averageProfile, div_eq_mul_inv, mul_comm]
  rw [havg, iteratedDeriv_const_smul_field]
  rw [iteratedDeriv_add hNext.contDiffAt hNow.contDiffAt]

theorem averageProfile_fourth_deriv_norm_bound
    (uNow uNext : ℝ → ℂ) (M : ℝ)
    (hNowC4 : ContDiff ℝ 4 uNow) (hNextC4 : ContDiff ℝ 4 uNext)
    (hNow : ∀ x, ‖iteratedDeriv 4 uNow x‖ ≤ M)
    (hNext : ∀ x, ‖iteratedDeriv 4 uNext x‖ ≤ M) :
    ∀ x, ‖iteratedDeriv 4 (averageProfile uNow uNext) x‖ ≤ M := by
  intro x
  rw [iteratedDeriv_averageProfile 4 uNow uNext x hNowC4 hNextC4]
  calc
    ‖(2 : ℂ)⁻¹ • (iteratedDeriv 4 uNext x + iteratedDeriv 4 uNow x)‖ =
        (1 / 2 : ℝ) * ‖iteratedDeriv 4 uNext x + iteratedDeriv 4 uNow x‖ := by
          rw [norm_smul]
          norm_num
    _ ≤ (1 / 2 : ℝ) *
        (‖iteratedDeriv 4 uNext x‖ + ‖iteratedDeriv 4 uNow x‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ M := by nlinarith [hNext x, hNow x, norm_nonneg (iteratedDeriv 4 uNext x)]

theorem sampled_average_schrodinger_relation
    (U : ℝ → ℝ → ℂ) (L k : ℝ) (m j : ℕ)
    (hSpaceC2 : ∀ t, ContDiff ℝ 2 (U t))
    (hSchrodinger : ∀ t x,
      iteratedDeriv 1 (timeProfile U x) t =
        Complex.I * iteratedDeriv 2 (U t) x) :
    (2 : ℂ)⁻¹ •
        (sampledTimeDerivative U L k m (j + 1) +
          sampledTimeDerivative U L k m j) =
      Complex.I • sampledSecondDerivative L (m + 1)
        (averageProfile (stepProfile U k j) (stepProfile U k (j + 1))) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, sampledTimeDerivative,
    sampledSecondDerivative]
  rw [hSchrodinger (((j + 1 : ℕ) : ℝ) * k) (gridPoint L (m + 1) i)]
  rw [hSchrodinger ((j : ℝ) * k) (gridPoint L (m + 1) i)]
  rw [iteratedDeriv_averageProfile 2
    (stepProfile U k j) (stepProfile U k (j + 1))
    (gridPoint L (m + 1) i) (hSpaceC2 ((j : ℝ) * k))
    (hSpaceC2 ((j + 1 : ℕ) * k))]
  simp only [stepProfile, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
-- Elaborating the fully specialized facade unfolds the long validated dependency chain.
theorem periodic_cayley_cn_convergence_of_smooth_solution
    (U : ℝ → ℝ → ℂ)
    (L : ℝ) (hL : 0 < L) (m : ℕ)
    (k T Mt Ms : ℝ) (hk : 0 < k) (hMt : 0 ≤ Mt)
    (hPeriodic : ∀ t, Function.Periodic (U t) L)
    (hSpaceC4 : ∀ t, ContDiff ℝ 4 (U t))
    (hSpace4 : ∀ t x, ‖iteratedDeriv 4 (U t) x‖ ≤ Ms)
    (hTimeC3 : ∀ x, ContDiff ℝ 3 (timeProfile U x))
    (hTime3 : ∀ x t, ‖iteratedDeriv 3 (timeProfile U x) t‖ ≤ Mt)
    (hSchrodinger : ∀ t x,
      iteratedDeriv 1 (timeProfile U x) t =
        Complex.I * iteratedDeriv 2 (U t) x)
    (numerical : ℕ → VecState (m + 1))
    (hnumerical : ∀ j, numerical (j + 1) =
      NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
          (k / 2) (periodicH L m)
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR
            (k / 2) (periodicH L m)))
        (numerical j))
    (N : ℕ) (horizon : (N : ℝ) * k ≤ T) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1))
        (sampledExactState L m (stepProfile U k) N - numerical N) ≤
      NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
          (meshWidth L (m + 1))
          (sampledExactState L m (stepProfile U k) 0 - numerical 0) +
        T * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
          (Real.sqrt L * (Ms / 12)) * meshWidth L (m + 1) ^ 2) := by
  apply periodic_cayley_cn_sampled_trajectory_fixed_time_error
    L hL m k T Mt Ms hk hMt (stepProfile U k)
      (sampledTimeDerivative U L k m) numerical
  · intro j
    exact sampled_average_schrodinger_relation U L k m j
      (fun t => (hSpaceC4 t).of_le (by norm_num)) hSchrodinger
  · intro j
    exact averageProfile_periodic _ _ L
      (hPeriodic ((j : ℝ) * k)) (hPeriodic ((j + 1 : ℕ) * k))
  · intro j
    exact averageProfile_contDiff_four _ _
      (hSpaceC4 ((j : ℝ) * k)) (hSpaceC4 ((j + 1 : ℕ) * k))
  · intro j
    exact averageProfile_fourth_deriv_norm_bound _ _ Ms
      (hSpaceC4 ((j : ℝ) * k)) (hSpaceC4 ((j + 1 : ℕ) * k))
      (hSpace4 ((j : ℝ) * k)) (hSpace4 ((j + 1 : ℕ) * k))
  · exact sampledCNTemporalResidual_norm_bound_of_uniform_time_regular
      U L k Mt m hk hTimeC3 hTime3
  · exact hnumerical
  · exact horizon

def analyticClosureStatus : String :=
  "smooth_periodic_solution_to_fixed_time_Ok2_plus_Oh2_convergence_validated"

end NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1
