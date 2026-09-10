import WeightedCayleyPropagation
import SamplingExpansion

/-! Actual finite-cutoff initial data, its sampled weighted norm, and the
scheduled ordered Cayley consumer. The cutoff is an Exp014 FourierState and
the sampling map is unchanged. Aliasing can only decrease the bound, so no
grid-resolution hypothesis or invariant finite solution band is needed.
The original Exp014 data are not assumed to have higher weighted moments.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

def finiteInitialCoefficients (s : Finset ℤ) (c : ℤ → E 2) (ell : ℤ) : E 2 :=
  if ell ∈ s then c ell else 0

theorem finiteInitialCoefficients_weighted_summable (s : Finset ℤ) (c : ℤ → E 2) :
    Summable (fun ell : ℤ => Exp014.weight ell * ‖finiteInitialCoefficients s c ell‖) := by
  apply (hasSum_sum_of_ne_finset_zero (s := s)
    (f := fun ell : ℤ => Exp014.weight ell * ‖finiteInitialCoefficients s c ell‖) ?_).summable
  intro ell hell
  simp only [finiteInitialCoefficients, if_neg hell, norm_zero, mul_zero]

/-- Finite input coefficients represented in the sealed complete state space. -/
def finiteInitialState (s : Finset ℤ) (c : ℤ → E 2) : Exp014.FourierState (E 2) :=
  Exp014.ofCoefficients (finiteInitialCoefficients s c)
    (finiteInitialCoefficients_weighted_summable s c)

theorem coefficient_finiteInitialState (s : Finset ℤ) (c : ℤ → E 2) (ell : ℤ) :
    Exp014.coefficient (finiteInitialState s c) ell = if ell ∈ s then c ell else 0 :=
  Exp014.coefficient_ofCoefficients _ _ ell

/-- The existing point-sampling map is exactly the finite sampled mode sum. -/
theorem sampledInitialState_finite_eq_sum (M : ℕ) (h : ℝ)
    (s : Finset ℤ) (c : ℤ → E 2) :
    sampledInitialState M h (finiteInitialState s c) =
      ∑ ell ∈ s, modeLiftCLM (2 * M) h ell (c ell) := by
  rw [sampledInitialState_eq_tsum]
  calc
    _ = ∑ ell ∈ s, modeLiftCLM (2 * M) h ell
        (Exp014.coefficient (finiteInitialState s c) ell) := by
      apply tsum_eq_sum
      intro ell hell
      simp only [coefficient_finiteInitialState, if_neg hell, map_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [coefficient_finiteInitialState, if_pos hell]

/-- A finite coefficient constant with no spatial-grid parameter. -/
def finiteInitialWeight (p : ℕ) (s : Finset ℤ) (c : ℤ → E 2) : ℝ :=
  ∑ ell ∈ s, frequencyWeight p ell * ‖c ell‖

theorem finiteInitialWeight_nonneg (p : ℕ) (s : Finset ℤ) (c : ℤ → E 2) :
    0 ≤ finiteInitialWeight p s c :=
  Finset.sum_nonneg fun ell _ => mul_nonneg (frequencyWeight_nonneg p ell) (norm_nonneg _)

/-- Actual normalized DFT samples, including unresolved aliases, obey the bound. -/
theorem sampledInitialState_finite_fourierWeightedNorm_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (s : Finset ℤ) (c : ℤ → E 2) :
    fourierWeightedNorm p M h (sampledInitialState M h (finiteInitialState s c)) ≤
      finiteInitialWeight p s c := by
  rw [sampledInitialState_finite_eq_sum]
  apply (fourierWeightedNorm_sum_le p M h s _).trans
  exact Finset.sum_le_sum fun ell _ => fourierWeightedNorm_modeLift_le p M h hmesh ell (c ell)

/-- The symmetric inclusive cutoff of the actual Exp014 initial coefficients. -/
def initialStateCutoff (R : ℕ) (a : Exp014.FourierState (E 2)) :
    Exp014.FourierState (E 2) :=
  finiteInitialState (Finset.Icc (-(R : ℤ)) (R : ℤ)) (Exp014.coefficient a)

theorem coefficient_initialStateCutoff (R : ℕ) (a : Exp014.FourierState (E 2))
    (ell : ℤ) :
    Exp014.coefficient (initialStateCutoff R a) ell =
      if |(ell : ℝ)| ≤ (R : ℝ) then Exp014.coefficient a ell else 0 := by
  have hm : ell ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) ↔ |(ell : ℝ)| ≤ (R : ℝ) := by
    constructor
    · intro he
      have hz : |ell| ≤ (R : ℤ) := abs_le.mpr (Finset.mem_Icc.mp he)
      exact_mod_cast hz
    · intro he
      have hz : |ell| ≤ (R : ℤ) := by exact_mod_cast he
      exact Finset.mem_Icc.mpr (abs_le.mp hz)
  simp only [initialStateCutoff, coefficient_finiteInitialState, hm]

def cutoffInitialWeight (p R : ℕ) (a : Exp014.FourierState (E 2)) : ℝ :=
  finiteInitialWeight p (Finset.Icc (-(R : ℤ)) (R : ℤ)) (Exp014.coefficient a)

theorem cutoffInitialWeight_nonneg (p R : ℕ) (a : Exp014.FourierState (E 2)) :
    0 ≤ cutoffInitialWeight p R a :=
  finiteInitialWeight_nonneg p _ _

/-- Uniform initial bound for actual samples of a fixed cutoff of the original data. -/
theorem sampledInitialState_cutoff_fourierWeightedNorm_le (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (a : Exp014.FourierState (E 2)) :
    fourierWeightedNorm p M h (sampledInitialState M h (initialStateCutoff R a)) ≤
      cutoffInitialWeight p R a :=
  sampledInitialState_finite_fourierWeightedNorm_le p M h hmesh _ _

/-- Every actual prefix up to time 1 is bounded by a fixed data/potential constant.
S and R are fixed independently of the numerical grid. The original data a
remain in the Exp014 class; finite fourth moments are used only after cutoff. -/
theorem scheduledCayley_doubleCutoff_fourierWeightedNorm_eventually_le (p S R : ℕ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState (E 2)) :
    ∀ᶠ q : ℕ in atTop, ∀ j ≤ temporalStepCount q,
      fourierWeightedNorm p (initialSamplingCutoff q) (initialSamplingMesh q)
        (sampledCayleyTrajectory (initialSamplingCutoff q) (initialSamplingMesh q)
          (potentialCutoff R v)
          (sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q) (initialStateCutoff S a))
          (fun _ => temporalStepSize q) j) ≤
      Real.exp (2 * (cutoffPotentialWeight p R v + 1)) * cutoffInitialWeight p S a := by
  filter_upwards [scheduledCayley_cutoff_fourierWeightedNorm_eventually_le p R v hHerm
    (fun q => sampledInitialState (initialSamplingCutoff q) (initialSamplingMesh q)
      (initialStateCutoff S a))] with q hq
  intro j hj
  apply (hq j hj).trans
  exact mul_le_mul_of_nonneg_left
    (sampledInitialState_cutoff_fourierWeightedNorm_le p (initialSamplingCutoff q) S
      (initialSamplingMesh q) (temporalSchedule_mesh q) a) (Real.exp_pos _).le

#print axioms finiteInitialCoefficients_weighted_summable
#print axioms coefficient_finiteInitialState
#print axioms sampledInitialState_finite_eq_sum
#print axioms finiteInitialWeight_nonneg
#print axioms sampledInitialState_finite_fourierWeightedNorm_le
#print axioms coefficient_initialStateCutoff
#print axioms cutoffInitialWeight_nonneg
#print axioms sampledInitialState_cutoff_fourierWeightedNorm_le
#print axioms scheduledCayley_doubleCutoff_fourierWeightedNorm_eventually_le
end NDEAEvolve.Exp016
