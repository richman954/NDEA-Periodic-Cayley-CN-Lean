import NDEAMathlibGate.PeriodicCayleyCNAnalyticClosureV1

/-! Passage from the explicit fixed-grid estimate to convergence along grid families. -/

noncomputable section

namespace NDEAMathlibGate.PeriodicCayleyCNGridFamilyConvergenceV1

open Filter Topology

def asymptoticErrorBound
    (L T Mt Ms initialError k h : ℝ) : ℝ :=
  initialError +
    T * ((Real.sqrt L * (5 * Mt / 12)) * k ^ 2 +
      (Real.sqrt L * (Ms / 12)) * h ^ 2)

theorem asymptoticErrorBound_tendsto_zero
    (L T Mt Ms : ℝ)
    (initialError k h : ℕ → ℝ)
    (hInitial : Tendsto initialError atTop (nhds 0))
    (hk : Tendsto k atTop (nhds 0))
    (hh : Tendsto h atTop (nhds 0)) :
    Tendsto (fun q => asymptoticErrorBound L T Mt Ms
      (initialError q) (k q) (h q)) atTop (nhds 0) := by
  have hk2 : Tendsto (fun q => k q ^ 2) atTop (nhds (0 ^ 2)) := hk.pow 2
  have hh2 : Tendsto (fun q => h q ^ 2) atTop (nhds (0 ^ 2)) := hh.pow 2
  have htime : Tendsto
      (fun q => (Real.sqrt L * (5 * Mt / 12)) * k q ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hk2)
  have hspace : Tendsto
      (fun q => (Real.sqrt L * (Ms / 12)) * h q ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hh2)
  have hconsistency : Tendsto
      (fun q => T *
        ((Real.sqrt L * (5 * Mt / 12)) * k q ^ 2 +
          (Real.sqrt L * (Ms / 12)) * h q ^ 2))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (htime.add hspace))
  simpa [asymptoticErrorBound] using hInitial.add hconsistency

theorem error_tendsto_zero_of_explicit_bound
    (L T Mt Ms : ℝ)
    (initialError k h error : ℕ → ℝ)
    (hInitial : Tendsto initialError atTop (nhds 0))
    (hk : Tendsto k atTop (nhds 0))
    (hh : Tendsto h atTop (nhds 0))
    (hErrorNonneg : ∀ q, 0 ≤ error q)
    (hEstimate : ∀ q, error q ≤ asymptoticErrorBound L T Mt Ms
      (initialError q) (k q) (h q)) :
    Tendsto error atTop (nhds 0) := by
  exact squeeze_zero hErrorNonneg hEstimate
    (asymptoticErrorBound_tendsto_zero L T Mt Ms initialError k h
      hInitial hk hh)

theorem exact_initialization_error_tendsto_zero
    (L T Mt Ms : ℝ)
    (k h error : ℕ → ℝ)
    (hk : Tendsto k atTop (nhds 0))
    (hh : Tendsto h atTop (nhds 0))
    (hErrorNonneg : ∀ q, 0 ≤ error q)
    (hEstimate : ∀ q, error q ≤
      T * ((Real.sqrt L * (5 * Mt / 12)) * k q ^ 2 +
        (Real.sqrt L * (Ms / 12)) * h q ^ 2)) :
    Tendsto error atTop (nhds 0) := by
  apply error_tendsto_zero_of_explicit_bound L T Mt Ms
    (fun _ => 0) k h error tendsto_const_nhds hk hh hErrorNonneg
  intro q
  simpa [asymptoticErrorBound] using hEstimate q

def gridFamilyConvergenceStatus : String :=
  "explicit_Ok2_plus_Oh2_bound_implies_grid_family_error_tends_to_zero"

end NDEAMathlibGate.PeriodicCayleyCNGridFamilyConvergenceV1
