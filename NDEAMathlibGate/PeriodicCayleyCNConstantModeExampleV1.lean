import NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1

/-! A fully instantiated constant periodic Schrödinger mode. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicCayleyCNConstantModeExampleV1

open Complex
open NDEAMathlibGate.CayleyEuclideanIsometryV1
open NDEAMathlibGate.PeriodicLaplacian1DSpatialConsistencyV1
open NDEAMathlibGate.PeriodicCayleyCrankNicolsonConvergenceV1
open NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1

def constantMode (c : ℂ) : ℝ → ℝ → ℂ :=
  fun _ _ => c

def constantModeNumerical
    (L k : ℝ) (m : ℕ) (c : ℂ) : ℕ → VecState (m + 1)
  | 0 => sampledExactState L m (stepProfile (constantMode c) k) 0
  | j + 1 =>
      NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
          (k / 2) (periodicH L m)
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR
            (k / 2) (periodicH L m)))
        (constantModeNumerical L k m c j)

theorem constantMode_periodic (c : ℂ) (L t : ℝ) :
    Function.Periodic (constantMode c t) L := by
  intro x
  rfl

theorem constantMode_space_C4 (c : ℂ) (t : ℝ) :
    ContDiff ℝ 4 (constantMode c t) := by
  change ContDiff ℝ 4 (fun _ : ℝ => c)
  fun_prop

theorem constantMode_time_C3 (c : ℂ) (x : ℝ) :
    ContDiff ℝ 3 (timeProfile (constantMode c) x) := by
  change ContDiff ℝ 3 (fun _ : ℝ => c)
  fun_prop

theorem constantMode_space_fourth_deriv_zero (c : ℂ) (t x : ℝ) :
    iteratedDeriv 4 (constantMode c t) x = 0 := by
  change iteratedDeriv 4 (fun _ : ℝ => c) x = 0
  rw [iteratedDeriv_const]
  norm_num

theorem constantMode_time_third_deriv_zero (c : ℂ) (x t : ℝ) :
    iteratedDeriv 3 (timeProfile (constantMode c) x) t = 0 := by
  change iteratedDeriv 3 (fun _ : ℝ => c) t = 0
  rw [iteratedDeriv_const]
  norm_num

theorem constantMode_schrodinger (c : ℂ) (t x : ℝ) :
    iteratedDeriv 1 (timeProfile (constantMode c) x) t =
      Complex.I * iteratedDeriv 2 (constantMode c t) x := by
  change iteratedDeriv 1 (fun _ : ℝ => c) t =
    Complex.I * iteratedDeriv 2 (fun _ : ℝ => c) x
  rw [iteratedDeriv_const, iteratedDeriv_const]
  norm_num

theorem constantModeNumerical_recurrence
    (L k : ℝ) (m : ℕ) (c : ℂ) (j : ℕ) :
    constantModeNumerical L k m c (j + 1) =
      NDEAMathlibGate.CayleyEuclideanIsometryV1.euclideanAction
        (NDEAMathlibGate.CayleyUnitaryFiniteV2WrapperR.cayleyU
          (k / 2) (periodicH L m)
          (NDEAMathlibGate.CayleyFactorInvertibilityFiniteV1.cayleyR
            (k / 2) (periodicH L m)))
        (constantModeNumerical L k m c j) := by
  rfl

theorem constantMode_fixed_time_error_zero_bound
    (c : ℂ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (k T : ℝ) (hk : 0 < k) (N : ℕ) (horizon : (N : ℝ) * k ≤ T) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1))
        (sampledExactState L m (stepProfile (constantMode c) k) N -
          constantModeNumerical L k m c N) ≤ 0 := by
  simpa [constantModeNumerical,
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm] using
    periodic_cayley_cn_convergence_of_smooth_solution
      (constantMode c) L hL m k T 0 0 hk (le_refl 0)
      (constantMode_periodic c L)
      (constantMode_space_C4 c)
      (fun t x => by simp [constantMode_space_fourth_deriv_zero])
      (constantMode_time_C3 c)
      (fun x t => by simp [constantMode_time_third_deriv_zero])
      (constantMode_schrodinger c)
      (constantModeNumerical L k m c)
      (constantModeNumerical_recurrence L k m c) N horizon

theorem constantMode_fixed_time_weighted_error_eq_zero
    (c : ℂ) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (k T : ℝ) (hk : 0 < k) (N : ℕ) (horizon : (N : ℝ) * k ≤ T) :
    NDEAMathlibGate.FiniteStateEuclideanNormBridgeV1.weightedNorm
        (meshWidth L (m + 1))
        (sampledExactState L m (stepProfile (constantMode c) k) N -
          constantModeNumerical L k m c N) = 0 := by
  apply le_antisymm
  · exact constantMode_fixed_time_error_zero_bound c L hL m k T hk N horizon
  · exact mul_nonneg (Real.sqrt_nonneg _)
      (norm_nonneg (sampledExactState L m (stepProfile (constantMode c) k) N -
        constantModeNumerical L k m c N))

def constantModeExampleStatus : String :=
  "all_analytic_hypotheses_instantiated_for_constant_periodic_mode"

end NDEAMathlibGate.PeriodicCayleyCNConstantModeExampleV1
