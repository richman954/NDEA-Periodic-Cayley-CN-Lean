import FiniteHorizonCertificate
import BaselineTimeOneConvergence

/-! Uniform convergence over every actual grid time, for each fixed T>0,
original Exp014 datum, and original regular Hermitian variable potential.
The finite maximum includes initialization and the endpoint. No continuous-
time interpolation limit or executable numerical certificate is asserted here.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
namespace NDEAEvolve.Exp016

def horizonGridError (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) : ℝ :=
  (Finset.range (temporalStepCount q + 1)).sup' ⟨0, by simp⟩ (fun N =>
    sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
      (fun _ => horizonStepSize T q) N b (actualCayleyTime (fun _ => horizonStepSize T q) N))

theorem horizonGridError_nonneg (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) : 0 ≤ horizonGridError v a b T q := by
  unfold horizonGridError
  exact Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.zero_lt_succ _))
    (Exp015.spatialL2_nonneg _ _ _)

theorem horizonGridError_le_iff (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) (B : ℝ) :
    horizonGridError v a b T q ≤ B ↔ ∀ N ≤ temporalStepCount q,
      sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
        (fun _ => horizonStepSize T q) N b (actualCayleyTime (fun _ => horizonStepSize T q) N) ≤ B := by
  unfold horizonGridError
  rw [Finset.sup'_le_iff]
  constructor
  · intro h N hN
    exact h N (Finset.mem_range.mpr (by omega))
  · intro h N hN
    exact h N (by have hn := Finset.mem_range.mp hN; omega)

/-- The maximum is over exactly t_N=N*k, not approximate comparison times. -/
theorem horizonGridError_eq_max_at_nk (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b T : ℝ) (q : ℕ) :
    horizonGridError v a b T q =
      (Finset.range (temporalStepCount q + 1)).sup' ⟨0, by simp⟩ (fun N =>
        sampledCayleySolutionError (initialSamplingCutoff q) (initialSamplingMesh q) v a
          (fun _ => horizonStepSize T q) N b ((N : ℝ) * horizonStepSize T q)) := by
  simp only [horizonGridError, actualCayleyTime_constant]

theorem horizonGridError_doubleCutoff_tendsto_zero (S R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (horizonGridError (potentialCutoff R v) (initialStateCutoff S a) b T) atTop (𝓝 0) := by
  apply squeeze_zero (horizonGridError_nonneg _ _ b T) _
    (horizonDoubleCutoffBudget_tendsto_zero S R T hT v hHerm a b)
  intro q
  apply (horizonGridError_le_iff _ _ b T q _).mpr
  intro N hN
  exact horizonCayley_gridTime_error_le T hT (potentialCutoff R v) (potentialCutoff_regular R v)
    (potentialCutoff_hermitian R v hHerm) (initialStateCutoff S a) b q N hN

theorem horizonGridError_initialCutoff_transfer (S : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) :
    horizonGridError v a b T q ≤ horizonGridError v (initialStateCutoff S a) b T q +
      2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S := by
  apply (horizonGridError_le_iff v a b T q _).mpr
  intro N hN
  have he := sampledCayley_initialCutoff_error_transfer _ S _ (temporalSchedule_mesh q)
    v hv hHerm a (fun _ => horizonStepSize T q) N b
    (actualCayleyTime (fun _ => horizonStepSize T q) N)
    (horizonSchedule_prefix_time_mem T hT q N hN).1
  apply he.trans
  exact add_le_add
    ((horizonGridError_le_iff v (initialStateCutoff S a) b T q _).mp le_rfl N hN) le_rfl

theorem horizonGridError_potentialCutoff_transfer (R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) :
    horizonGridError v a b T q ≤ horizonGridError (potentialCutoff R v) a b T q +
      2 * T * frequencyNormTail v R * (Real.sqrt (2 * Real.pi) * ‖a‖) := by
  apply (horizonGridError_le_iff v a b T q _).mpr
  intro N hN
  have he := sampledCayley_gridTime_cutoff_error_transfer _ R _ (temporalSchedule_mesh q)
    v hv hHerm a (fun _ => horizonStepSize T q) N b
    (fun _ _ => (horizonStepSize_pos T hT q).le)
  apply he.trans
  apply add_le_add
  · exact (horizonGridError_le_iff (potentialCutoff R v) a b T q _).mp le_rfl N hN
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (horizonSchedule_prefix_time_mem T hT q N hN).2 (by norm_num))
        (frequencyNormTail_nonneg v R)) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

theorem horizonGridError_potentialCutoff_tendsto_zero (R : ℕ) (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (horizonGridError (potentialCutoff R v) a b T) atTop (𝓝 0) := by
  apply tendsto_zero_of_uniform_approximation _
    (fun S => horizonGridError (potentialCutoff R v) (initialStateCutoff S a) b T)
    (fun S => 2 * Real.sqrt (2 * Real.pi) * frequencyNormTail (Exp014.coefficient a) S)
  · exact horizonGridError_nonneg _ a b T
  · intro S q
    exact horizonGridError_initialCutoff_transfer S T hT (potentialCutoff R v)
      (potentialCutoff_regular R v) (potentialCutoff_hermitian R v hHerm) a b q
  · intro S
    exact horizonGridError_doubleCutoff_tendsto_zero S R T hT v hHerm a b
  · simpa only [mul_zero] using
      (frequencyNormTail_tendsto_zero (Exp014.coefficient a) (Exp014.coefficient_summable_norm a)
        (Exp014.weighted_summable a) id tendsto_id).const_mul (2 * Real.sqrt (2 * Real.pi))

/-- Uniform grid-time convergence in the original variable-potential class. -/
theorem horizonGridError_tendsto_zero (T : ℝ) (hT : 0 < T)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (horizonGridError v a b T) atTop (𝓝 0) := by
  apply tendsto_zero_of_uniform_approximation _
    (fun R => horizonGridError (potentialCutoff R v) a b T)
    (fun R => 2 * T * frequencyNormTail v R * (Real.sqrt (2 * Real.pi) * ‖a‖))
  · exact horizonGridError_nonneg v a b T
  · intro R q
    exact horizonGridError_potentialCutoff_transfer R T hT v hv hHerm a b q
  · intro R
    exact horizonGridError_potentialCutoff_tendsto_zero R T hT v hHerm a b
  · simpa only [mul_zero, zero_mul] using
      ((frequencyNormTail_tendsto_zero v (Exp014.regularPotential_absolute v hv) hv id tendsto_id)
        .const_mul (2 * T)).mul_const (Real.sqrt (2 * Real.pi) * ‖a‖)

#print axioms horizonGridError_nonneg
#print axioms horizonGridError_le_iff
#print axioms horizonGridError_eq_max_at_nk
#print axioms horizonGridError_doubleCutoff_tendsto_zero
#print axioms horizonGridError_initialCutoff_transfer
#print axioms horizonGridError_potentialCutoff_transfer
#print axioms horizonGridError_potentialCutoff_tendsto_zero
#print axioms horizonGridError_tendsto_zero
end NDEAEvolve.Exp016
