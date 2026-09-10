import TemporalBudget
import InitialSamplingLimit

/-! Temporal refinement of the actual sampled ordered Cayley trajectory.
The schedule is the recorded full odd grid with M=q+1, J=N^4, k=1/J, T=1.
The actual accumulated temporal contribution tends to zero. The final error
certificate retains every computed spatial contribution; solver convergence
does not follow until that spatial sum is controlled. -/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def temporalGridSize (q : ℕ) : ℕ := 2 * initialSamplingCutoff q + 1
def temporalStepCount (q : ℕ) : ℕ := temporalGridSize q ^ 4
def temporalStepSize (q : ℕ) : ℝ := (temporalStepCount q : ℝ)⁻¹

theorem temporalGridSize_pos (q : ℕ) : 0 < temporalGridSize q := by
  unfold temporalGridSize
  positivity

theorem temporalStepCount_pos (q : ℕ) : 0 < temporalStepCount q :=
  pow_pos (temporalGridSize_pos q) 4

theorem temporalStepSize_pos (q : ℕ) : 0 < temporalStepSize q := by
  unfold temporalStepSize
  exact inv_pos.mpr (by exact_mod_cast temporalStepCount_pos q)

theorem temporalSchedule_mesh (q : ℕ) :
    ((2 * initialSamplingCutoff q + 1 : ℕ) : ℝ) * initialSamplingMesh q =
      2 * Real.pi := by
  unfold initialSamplingMesh
  exact mul_div_cancel₀ _ (by positivity)

theorem temporalSchedule_mesh_pos (q : ℕ) : 0 < initialSamplingMesh q := by
  unfold initialSamplingMesh
  positivity

private theorem tr_actualTime_const (k : ℝ) (J : ℕ) :
    actualCayleyTime (fun _ => k) J = (J : ℝ) * k := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [actualCayleyTime_succ, ih]
    push_cast
    ring

/-- The refinement comparison is at the actual time 1, not a nearby grid time. -/
theorem temporalSchedule_time_one (q : ℕ) :
    actualCayleyTime (fun _ => temporalStepSize q) (temporalStepCount q) = 1 := by
  rw [tr_actualTime_const, temporalStepSize]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt (temporalStepCount_pos q)))

theorem temporalSchedule_sum_cube (q : ℕ) :
    (∑ _j ∈ Finset.range (temporalStepCount q), (temporalStepSize q)^3) =
      (temporalStepSize q)^2 := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, temporalStepSize]
  have hn : (temporalStepCount q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (temporalStepCount_pos q))
  field_simp [hn]

/-- Exact normalization of the growing mesh coefficient. After multiplying
by k²=N⁻⁸, only N⁻² times a polynomial in N⁻² remains. -/
theorem physicalTemporalCoefficient_rescaled (n : ℝ) (hn : n ≠ 0)
    (v : ℤ → E 2 →L[ℂ] E 2) :
    ((n^4)⁻¹)^2 * physicalTemporalCoefficient (2 * Real.pi / n) v =
      (n⁻¹)^2 * temporalOperatorCoefficient ((Real.pi⁻¹)^2 + (n⁻¹)^2)
        (((∑' ell : ℤ, ‖v ell‖) + 1) * (n⁻¹)^2) := by
  unfold physicalTemporalCoefficient temporalOperatorCoefficient
  field_simp [hn, Real.pi_ne_zero]
  ring

private theorem tr_coefficient_tendsto {α : Type*} {l : Filter α}
    {f g : α → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun q => temporalOperatorCoefficient (f q) (g q)) l
      (𝓝 (temporalOperatorCoefficient a b)) := by
  exact ((hf.mul ((hf.add (hg.const_mul 2)).pow 2)).div_const 16).add
    (((hf.add hg).pow 3).div_const 8)

theorem temporalGridSize_tendsto_atTop : Tendsto temporalGridSize atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨b, fun q hq => by
    unfold temporalGridSize initialSamplingCutoff
    omega⟩

theorem scheduledTemporalCoefficient_tendsto_zero
    (v : ℤ → E 2 →L[ℂ] E 2) :
    Tendsto (fun q => (temporalStepSize q)^2 *
      physicalTemporalCoefficient (initialSamplingMesh q) v) atTop (𝓝 0) := by
  have hi : Tendsto (fun q => (temporalGridSize q : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp temporalGridSize_tendsto_atTop
  have hs : Tendsto (fun q => ((temporalGridSize q : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hi.pow 2
  have hc := tr_coefficient_tendsto
    (hs.const_add ((Real.pi⁻¹)^2))
    (hs.const_mul ((∑' ell : ℤ, ‖v ell‖) + 1))
  have hz := hs.mul hc
  simp only [zero_mul] at hz
  convert hz using 1
  funext q
  have hn : (temporalGridSize q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (temporalGridSize_pos q))
  simpa only [temporalStepSize, temporalStepCount, Nat.cast_pow,
    initialSamplingMesh, temporalGridSize] using
      physicalTemporalCoefficient_rescaled (temporalGridSize q : ℝ) hn v

def scheduledTemporalBound (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (q : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * ‖a‖) *
    ((temporalStepSize q)^2 * physicalTemporalCoefficient (initialSamplingMesh q) v)

theorem scheduledTemporalBound_tendsto_zero (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) :
    Tendsto (scheduledTemporalBound v a) atTop (𝓝 0) := by
  change Tendsto (fun q => scheduledTemporalBound v a q) atTop (𝓝 0)
  simpa only [scheduledTemporalBound, mul_zero] using
    (scheduledTemporalCoefficient_tendsto_zero v).const_mul (Real.sqrt (2 * Real.pi) * ‖a‖)

private theorem tr_initial_norm_budget (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (q : ℕ) :
    (Real.sqrt (initialSamplingMesh q) *
      ‖sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a‖) *
      physicalTemporalCoefficient (initialSamplingMesh q) v * (temporalStepSize q)^2 ≤
      scheduledTemporalBound v a q := by
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (sampledInitialState_weighted_norm_le_state _ _ (temporalSchedule_mesh q) a)
      (physicalTemporalCoefficient_nonneg _ v)) (sq_nonneg (temporalStepSize q))).trans_eq
  unfold scheduledTemporalBound
  ring

/-- The bound controls the temporal sum of the actual ordered trajectory
started from actual point samples of Exp014 data. -/
theorem scheduledSampledTemporalSum_le (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (q : ℕ) :
    sampledTemporalSum (initialSamplingCutoff q) (initialSamplingMesh q) v
      (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
      (fun _ => temporalStepSize q) (temporalStepCount q) ≤ scheduledTemporalBound v a q := by
  have h := sampledTemporalSum_le_physical _ _ (temporalSchedule_mesh q)
    (temporalSchedule_mesh_pos q) v hv hHerm
    (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
    (fun _ => temporalStepSize q) (temporalStepCount q)
    (fun _ _ => (temporalStepSize_pos q).le)
  rw [temporalSchedule_sum_cube] at h
  exact h.trans (tr_initial_norm_budget v a q)

theorem scheduledSampledTemporalSum_tendsto_zero (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) :
    Tendsto (fun q => sampledTemporalSum (initialSamplingCutoff q) (initialSamplingMesh q) v
      (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
      (fun _ => temporalStepSize q) (temporalStepCount q)) atTop (𝓝 0) :=
  squeeze_zero
    (fun q => sampledTemporalSum_nonneg _ _ v _ _ _ (fun _ _ => (temporalStepSize_pos q).le))
    (scheduledSampledTemporalSum_le v hv hHerm a) (scheduledTemporalBound_tendsto_zero v a)

def scheduledInitialError (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) : ℝ :=
  Exp015.spatialL2 (fun x => IndependentTarget.rawFourier (initialSamplingCutoff q)
    (initialSamplingMesh q)
    (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a) x -
      Exp014.synth a x) b (2 * Real.pi)

def scheduledSpatialSum (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) : ℝ :=
  let M := initialSamplingCutoff q
  let h := initialSamplingMesh q
  let k := fun _ : ℕ => temporalStepSize q
  let y₀ := sampledInitialState M h a
  ∑ j ∈ Finset.range (temporalStepCount q), k j *
    sampledSpatialStageBudget M h v (sampledCayleyTrajectory M h v y₀ k j) b (k j)

/-- At exact time 1 the actual error is bounded by the initialization,
the proved vanishing temporal bound, and the unresolved actual spatial sum. -/
theorem scheduledCayley_error_le (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) (b : ℝ) (q : ℕ) :
    Exp015.spatialL2 (fun x => IndependentTarget.rawFourier (initialSamplingCutoff q)
      (initialSamplingMesh q)
      (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q) v
        (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a)
        (fun _ => temporalStepSize q) (temporalStepCount q)) x -
      Exp014.solution v a 1 x) b (2 * Real.pi) ≤
      scheduledInitialError a b q + scheduledTemporalBound v a q + scheduledSpatialSum v a b q := by
  have he := sampledCayley_gridTime_explicitTemporal_error _ _ (temporalSchedule_mesh q)
    (temporalSchedule_mesh_pos q) v hv hHerm a
    (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) a) b
    (fun _ => temporalStepSize q) (temporalStepCount q) (fun _ _ => temporalStepSize_pos q)
  rw [temporalSchedule_time_one, temporalSchedule_sum_cube] at he
  exact he.trans (add_le_add (add_le_add le_rfl (tr_initial_norm_budget v a q)) le_rfl)

/-- All nonspatial terms of this actual certificate vanish. This theorem
deliberately makes no assertion that the spatial sum vanishes. -/
theorem scheduledNonspatialBudget_tendsto_zero (v : ℤ → E 2 →L[ℂ] E 2)
    (a : Exp014.FourierState (E 2)) (b : ℝ) :
    Tendsto (fun q => scheduledInitialError a b q + scheduledTemporalBound v a q)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun q => scheduledInitialError a b q) atTop (𝓝 0) := by
    simpa only [scheduledInitialError, ← fourierReconstruction_eq_independentTarget] using
      scheduledInitialSampling_spatialL2_tendsto_zero a b
  simpa only [add_zero] using hi.add (scheduledTemporalBound_tendsto_zero v a)

#print axioms temporalGridSize_pos
#print axioms temporalStepCount_pos
#print axioms temporalStepSize_pos
#print axioms temporalSchedule_mesh
#print axioms temporalSchedule_mesh_pos
#print axioms temporalSchedule_time_one
#print axioms temporalSchedule_sum_cube
#print axioms physicalTemporalCoefficient_rescaled
#print axioms temporalGridSize_tendsto_atTop
#print axioms scheduledTemporalCoefficient_tendsto_zero
#print axioms scheduledTemporalBound_tendsto_zero
#print axioms scheduledSampledTemporalSum_le
#print axioms scheduledSampledTemporalSum_tendsto_zero
#print axioms scheduledCayley_error_le
#print axioms scheduledNonspatialBudget_tendsto_zero
end NDEAEvolve.Exp016
