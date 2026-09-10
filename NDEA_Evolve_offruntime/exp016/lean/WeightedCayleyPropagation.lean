import WeightedGridStages
import TemporalRefinement

/-! Weighted growth of the actual ordered Cayley trajectory for fixed cutoffs.
The B constant includes -Z, the A factors preserve the weight, and the exact
denominator equation supplies the estimate. Signed variable steps are allowed
under an explicit small-step bound. The saved refinement schedule eventually
satisfies that bound. Initial weighted amplitudes and spatial refinement are
separate obligations, not premises asserting their own convergence.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

/-- The actual Cayley equation gives the weighted resolvent/step factor. -/
theorem fourierWeightedNorm_cayley_step_le (p M : ℕ) (h a : ℝ)
    (G : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ) (hG : G.IsHermitian)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ y, fourierWeightedNorm p M h (op G y) ≤ K * fourierWeightedNorm p M h y)
    (hsmall : |a| * K < 1) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (step a G y) ≤
      ((1 + |a| * K) / (1 - |a| * K)) * fourierWeightedNorm p M h y := by
  let z := step a G y
  have hz : z - y + (Complex.I * (a : ℂ)) • op G (z + y) = 0 :=
    stageResidual_actual_cayley_zero G a hG y
  have he : z = y - (Complex.I * (a : ℂ)) • op G (z + y) := by
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = (z - y + (Complex.I * (a : ℂ)) • op G (z + y)) + y := by abel
      _ = y := by rw [hz, zero_add]
  have hn : fourierWeightedNorm p M h z ≤ fourierWeightedNorm p M h y +
      (|a| * K) * (fourierWeightedNorm p M h z + fourierWeightedNorm p M h y) := by
    calc
      _ = fourierWeightedNorm p M h (y - (Complex.I * (a : ℂ)) • op G (z + y)) :=
        congrArg (fourierWeightedNorm p M h) he
      _ ≤ fourierWeightedNorm p M h y +
          fourierWeightedNorm p M h ((Complex.I * (a : ℂ)) • op G (z + y)) :=
        fourierWeightedNorm_sub_le p M h _ _
      _ = fourierWeightedNorm p M h y + |a| * fourierWeightedNorm p M h (op G (z + y)) := by
        rw [fourierWeightedNorm_smul, norm_mul, Complex.norm_I,
          Complex.norm_real, Real.norm_eq_abs, one_mul]
      _ ≤ fourierWeightedNorm p M h y + |a| * (K * fourierWeightedNorm p M h (z + y)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbound (z + y)) (abs_nonneg a))
      _ ≤ fourierWeightedNorm p M h y + |a| *
          (K * (fourierWeightedNorm p M h z + fourierWeightedNorm p M h y)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (fourierWeightedNorm_add_le p M h z y) hK) (abs_nonneg a))
      _ = _ := by ring
  change fourierWeightedNorm p M h z ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 1 - |a| * K by linarith)).mpr
  nlinarith [hn]

/-- A coarse exponential bound suitable for finite-time products. -/
theorem weightedCayleyFactor_le_exp (x : ℝ) (hx : 0 ≤ x) (hsmall : x ≤ 1 / 2) :
    (1 + x) / (1 - x) ≤ Real.exp (4 * x) := by
  calc
    _ ≤ 1 + 4 * x := by
      apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
      nlinarith [mul_nonneg hx (show 0 ≤ 1 / 2 - x by linarith)]
    _ ≤ _ := by linarith [Real.add_one_le_exp (4 * x)]

theorem fourierWeightedNorm_cayley_step_exp_le (p M : ℕ) (h a : ℝ)
    (G : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ) (hG : G.IsHermitian)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ y, fourierWeightedNorm p M h (op G y) ≤ K * fourierWeightedNorm p M h y)
    (hsmall : |a| * K ≤ 1 / 2) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (step a G y) ≤
      Real.exp (4 * |a| * K) * fourierWeightedNorm p M h y := by
  have hx : 0 ≤ |a| * K := mul_nonneg (abs_nonneg a) hK
  calc
    _ ≤ ((1 + |a| * K) / (1 - |a| * K)) * fourierWeightedNorm p M h y :=
      fourierWeightedNorm_cayley_step_le p M h a G hG K hK hbound (by linarith) y
    _ ≤ Real.exp (4 * (|a| * K)) * fourierWeightedNorm p M h y :=
      mul_le_mul_of_nonneg_right (weightedCayleyFactor_le_exp _ hx hsmall)
        (fourierWeightedNorm_nonneg p M h y)
    _ = _ := by rw [mul_assoc]

/-- The actual B-full stage has a mesh-independent weighted growth bound. -/
theorem fourierWeightedNorm_sampledSplitB_step_cutoff_le (p M R : ℕ) (h k : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (hsmall : |k| * (cutoffPotentialWeight p R v + 1) ≤ 1) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h
      (step (k / 2) (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) y) ≤
        Real.exp (2 * |k| * (cutoffPotentialWeight p R v + 1)) * fourierWeightedNorm p M h y := by
  have hK : 0 ≤ cutoffPotentialWeight p R v + 1 := by
    linarith [cutoffPotentialWeight_nonneg p R v]
  have hs : |k / 2| * (cutoffPotentialWeight p R v + 1) ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have he : 4 * |k / 2| * (cutoffPotentialWeight p R v + 1) =
      2 * |k| * (cutoffPotentialWeight p R v + 1) := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    ring
  simpa only [he] using fourierWeightedNorm_cayley_step_exp_le p M h (k / 2) _
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h _ (potentialCutoff_hermitian R v hHerm))
    (cutoffPotentialWeight p R v + 1) hK
    (fourierWeightedNorm_sampledSplitB_cutoff_le p M R h hmesh v) hs y

/-- Exact A-half/B-full/A-half order; both actual A factors preserve the weight. -/
theorem orderedCayleyEndpoint_cutoff_fourierWeightedNorm_le (p M R : ℕ) (h k : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (hsmall : |k| * (cutoffPotentialWeight p R v + 1) ≤ 1) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h
      (orderedCayleyEndpoint (sampledSplitA (2 * M) h)
        (sampledSplitB (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) k y) ≤
      Real.exp (2 * |k| * (cutoffPotentialWeight p R v + 1)) * fourierWeightedNorm p M h y := by
  unfold orderedCayleyEndpoint
  rw [fourierWeightedNorm_sampledSplitA_step p M h (k / 4) hmesh]
  have hb := fourierWeightedNorm_sampledSplitB_step_cutoff_le p M R h k hmesh v hHerm hsmall
    (step (k / 4) (sampledSplitA (2 * M) h) y)
  rw [fourierWeightedNorm_sampledSplitA_step p M h (k / 4) hmesh] at hb
  exact hb

/-- Actual finite trajectories, with signed variable steps and explicit restrictions. -/
theorem sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ) :
    (∀ j < N, |k j| * (cutoffPotentialWeight p R v + 1) ≤ 1) →
    fourierWeightedNorm p M h (sampledCayleyTrajectory M h (potentialCutoff R v) y k N) ≤
      Real.exp (2 * (cutoffPotentialWeight p R v + 1) * (∑ j ∈ Finset.range N, |k j|)) *
        fourierWeightedNorm p M h y := by
  induction N with
  | zero => intro _; simp [sampledCayleyTrajectory]
  | succ N ih =>
    intro hstep
    have hp := ih (fun j hj => hstep j (by omega))
    change fourierWeightedNorm p M h (actualCayleyTrajectory _ _ y k (N + 1)) ≤ _
    rw [actualCayleyTrajectory_succ]
    calc
      _ ≤ Real.exp (2 * |k N| * (cutoffPotentialWeight p R v + 1)) *
          fourierWeightedNorm p M h (sampledCayleyTrajectory M h (potentialCutoff R v) y k N) :=
        orderedCayleyEndpoint_cutoff_fourierWeightedNorm_le p M R h (k N) hmesh v hHerm
          (hstep N (by omega)) _
      _ ≤ Real.exp (2 * |k N| * (cutoffPotentialWeight p R v + 1)) *
          (Real.exp (2 * (cutoffPotentialWeight p R v + 1) * (∑ j ∈ Finset.range N, |k j|)) *
            fourierWeightedNorm p M h y) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add, Finset.sum_range_succ]
        congr 2 <;> ring

theorem sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le_horizon (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y : Vec (Grid (2 * M))) (k : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ j < N, |k j| * (cutoffPotentialWeight p R v + 1) ≤ 1)
    (T : ℝ) (hT : (∑ j ∈ Finset.range N, |k j|) ≤ T) :
    fourierWeightedNorm p M h (sampledCayleyTrajectory M h (potentialCutoff R v) y k N) ≤
      Real.exp (2 * (cutoffPotentialWeight p R v + 1) * T) * fourierWeightedNorm p M h y := by
  apply (sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le p M R h hmesh v hHerm y k N hstep).trans
  apply mul_le_mul_of_nonneg_right _ (fourierWeightedNorm_nonneg p M h y)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hT (by linarith [cutoffPotentialWeight_nonneg p R v])

theorem temporalStepSize_tendsto_zero : Tendsto temporalStepSize atTop (𝓝 0) := by
  have hi : Tendsto (fun q => (temporalGridSize q : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp temporalGridSize_tendsto_atTop
  change Tendsto (fun q => temporalStepSize q) atTop (𝓝 0)
  simpa only [temporalStepSize, temporalStepCount, Nat.cast_pow, inv_pow,
    zero_pow (by decide : 4 ≠ 0)] using hi.pow 4

/-- Every fixed weighted potential constant eventually meets the actual step restriction. -/
theorem eventually_temporalStepSize_mul_le_one (K : ℝ) :
    ∀ᶠ q : ℕ in atTop, |temporalStepSize q| * K ≤ 1 := by
  have hz : Tendsto (fun q => temporalStepSize q * K) atTop (𝓝 0) := by
    simpa only [zero_mul] using temporalStepSize_tendsto_zero.mul_const K
  have he := hz.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [he] with q hq
  rw [abs_of_pos (temporalStepSize_pos q)]
  exact hq.le

/-- Every actual grid-time prefix up to T=1 has the same grid-independent factor,
eventually on the saved N, h, J, k refinement schedule. Initial W_p remains explicit. -/
theorem scheduledCayley_cutoff_fourierWeightedNorm_eventually_le (p R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (y : (q : ℕ) → Vec (Grid (2 * initialSamplingCutoff q))) :
    ∀ᶠ q : ℕ in atTop, ∀ j ≤ temporalStepCount q,
      fourierWeightedNorm p (initialSamplingCutoff q) (initialSamplingMesh q)
        (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q)
          (potentialCutoff R v) (y q) (fun _ => temporalStepSize q) j) ≤
      Real.exp (2 * (cutoffPotentialWeight p R v + 1)) *
        fourierWeightedNorm p (initialSamplingCutoff q) (initialSamplingMesh q) (y q) := by
  filter_upwards [eventually_temporalStepSize_mul_le_one (cutoffPotentialWeight p R v + 1)] with q hq
  intro j hj
  have hT : (∑ _i ∈ Finset.range j, |temporalStepSize q|) ≤ (1 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      abs_of_pos (temporalStepSize_pos q)]
    calc
      (j : ℝ) * temporalStepSize q ≤ (temporalStepCount q : ℝ) * temporalStepSize q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (temporalStepSize_pos q).le
      _ = 1 := by
        unfold temporalStepSize
        exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt (temporalStepCount_pos q)))
  simpa only [mul_one] using sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le_horizon
    p (initialSamplingCutoff q) R (initialSamplingMesh q) (temporalSchedule_mesh q)
    v hHerm (y q) (fun _ => temporalStepSize q) j (fun _ _ => hq) 1 hT

#print axioms fourierWeightedNorm_cayley_step_le
#print axioms weightedCayleyFactor_le_exp
#print axioms fourierWeightedNorm_cayley_step_exp_le
#print axioms fourierWeightedNorm_sampledSplitB_step_cutoff_le
#print axioms orderedCayleyEndpoint_cutoff_fourierWeightedNorm_le
#print axioms sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le
#print axioms sampledCayleyTrajectory_cutoff_fourierWeightedNorm_le_horizon
#print axioms temporalStepSize_tendsto_zero
#print axioms eventually_temporalStepSize_mul_le_one
#print axioms scheduledCayley_cutoff_fourierWeightedNorm_eventually_le
end NDEAEvolve.Exp016
