import AliasWeights
import PotentialAlias
import PotentialCutoff

/-! Mesh-independent weighted bounds for actual sampled potential multiplication.
Finite potential support is used explicitly; arbitrary grid states and aliases
are retained. In particular, no invariant finite solution band is assumed.
For p = 2 the constant is the finite fourth weighted coefficient sum.
This does not assert a finite fourth moment for every Exp014 regular potential.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

/-- A potential with the stated finite support satisfies Exp014 regularity. -/
theorem finitePotential_regular (s : Finset ℤ) (v : ℤ → E 2 →L[ℂ] E 2)
    (hv : ∀ ell ∉ s, v ell = 0) : Exp014.RegularPotential v := by
  apply (hasSum_sum_of_ne_finset_zero (s := s)
    (f := fun ell : ℤ => Exp014.weight ell * ‖v ell‖) ?_).summable
  intro ell hell
  rw [hv ell hell, norm_zero, mul_zero]

/-- Exact finite series for the actual sampled action on an arbitrary integer mode. -/
theorem sampledPotential_on_modeLift_finset (n : ℕ) (h : ℝ) (m : ℤ)
    (s : Finset ℤ) (v : ℤ → E 2 →L[ℂ] E 2) (hv : ∀ ell ∉ s, v ell = 0)
    (u : E 2) :
    op (sampledBlock n h (operatorPotentialMatrix v)) (modeLiftCLM n h m u) =
      ∑ ell ∈ s, modeLiftCLM n h (ell + m) (v ell u) := by
  rw [sampledPotential_on_modeLift n h m v (finitePotential_regular s v hv)]
  apply tsum_eq_sum
  intro ell hell
  simp only [hv ell hell, ContinuousLinearMap.zero_apply, map_zero]

/-- The finite coefficient constant contains no spatial grid parameter. -/
def finitePotentialWeight (p : ℕ) (s : Finset ℤ) (v : ℤ → E 2 →L[ℂ] E 2) : ℝ :=
  ∑ ell ∈ s, frequencyWeight p ell * ‖v ell‖

theorem finitePotentialWeight_nonneg (p : ℕ) (s : Finset ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) : 0 ≤ finitePotentialWeight p s v :=
  Finset.sum_nonneg fun ell _ => mul_nonneg (frequencyWeight_nonneg p ell) (norm_nonneg _)

/-- Each actual shifted mode is controlled by the product of input/potential weights. -/
theorem fourierWeightedNorm_potential_mode_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell m : ℤ) (V : E 2 →L[ℂ] E 2) (u : E 2) :
    fourierWeightedNorm p M h (modeLiftCLM (2 * M) h (ell + m) (V u)) ≤
      (frequencyWeight p ell * ‖V‖) * (frequencyWeight p m * ‖u‖) := by
  calc
    _ ≤ frequencyWeight p (ell + m) * ‖V u‖ :=
      fourierWeightedNorm_modeLift_le p M h hmesh (ell + m) (V u)
    _ ≤ (frequencyWeight p ell * frequencyWeight p m) * (‖V‖ * ‖u‖) :=
      mul_le_mul (frequencyWeight_add_le p ell m) (V.le_opNorm u)
        (norm_nonneg _) (mul_nonneg (frequencyWeight_nonneg p ell) (frequencyWeight_nonneg p m))
    _ = _ := by ring

/-- The actual sampled multiplication operator is bounded in the weighted DFT sum.
The constant has no N factor, and no relation between s and the grid band is needed. -/
theorem fourierWeightedNorm_sampledPotential_le (p M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (s : Finset ℤ) (v : ℤ → E 2 →L[ℂ] E 2) (hv : ∀ ell ∉ s, v ell = 0)
    (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y) ≤
      finitePotentialWeight p s v * fourierWeightedNorm p M h y := by
  have he : op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y =
      ∑ m : Fin (2 * M + 1), ∑ ell ∈ s,
        modeLiftCLM (2 * M) h (ell + oddFrequency M m)
          (v ell (fourierCoefficient M h y m)) := by
    calc
      _ = op (sampledBlock (2 * M) h (operatorPotentialMatrix v))
          (∑ m : Fin (2 * M + 1), modeLiftCLM (2 * M) h (oddFrequency M m)
            (fourierCoefficient M h y m)) :=
        congrArg (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)))
          (gridState_eq_modeLift_sum M h hmesh y)
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro m _
        exact sampledPotential_on_modeLift_finset (2 * M) h (oddFrequency M m) s v hv _
  rw [he]
  calc
    _ ≤ ∑ m : Fin (2 * M + 1), fourierWeightedNorm p M h
        (∑ ell ∈ s, modeLiftCLM (2 * M) h (ell + oddFrequency M m)
          (v ell (fourierCoefficient M h y m))) :=
      fourierWeightedNorm_sum_le p M h Finset.univ _
    _ ≤ ∑ m : Fin (2 * M + 1), finitePotentialWeight p s v *
        (frequencyWeight p (oddFrequency M m) * ‖fourierCoefficient M h y m‖) := by
      apply Finset.sum_le_sum
      intro m _
      calc
        _ ≤ ∑ ell ∈ s, fourierWeightedNorm p M h
            (modeLiftCLM (2 * M) h (ell + oddFrequency M m)
              (v ell (fourierCoefficient M h y m))) :=
          fourierWeightedNorm_sum_le p M h s _
        _ ≤ ∑ ell ∈ s, (frequencyWeight p ell * ‖v ell‖) *
            (frequencyWeight p (oddFrequency M m) * ‖fourierCoefficient M h y m‖) := by
          apply Finset.sum_le_sum
          intro ell _
          exact fourierWeightedNorm_potential_mode_le p M h hmesh ell (oddFrequency M m) _ _
        _ = _ := by rw [finitePotentialWeight, Finset.sum_mul]
    _ = _ := by rw [fourierWeightedNorm, Finset.mul_sum]

/-- The inclusive cutoff's weighted constant uses exactly its retained original coefficients. -/
def cutoffPotentialWeight (p R : ℕ) (v : ℤ → E 2 →L[ℂ] E 2) : ℝ :=
  finitePotentialWeight p (Finset.Icc (-(R : ℤ)) (R : ℤ)) v

theorem cutoffPotentialWeight_nonneg (p R : ℕ) (v : ℤ → E 2 →L[ℂ] E 2) :
    0 ≤ cutoffPotentialWeight p R v := finitePotentialWeight_nonneg p _ v

/-- Concrete consumer for the already accepted potential cutoff/stability route.
The original v is arbitrary; only its fixed finite cutoff is used by this bound. -/
theorem fourierWeightedNorm_sampledPotential_cutoff_le (p M R : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid (2 * M))) :
    fourierWeightedNorm p M h
      (op (sampledBlock (2 * M) h (operatorPotentialMatrix (potentialCutoff R v))) y) ≤
        cutoffPotentialWeight p R v * fourierWeightedNorm p M h y := by
  let s : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hv : ∀ ell ∉ s, potentialCutoff R v ell = 0 := by
    intro ell hell
    have hn : ¬ |(ell : ℝ)| ≤ (R : ℝ) := by
      intro he
      have hz : |ell| ≤ (R : ℤ) := by exact_mod_cast he
      exact hell (Finset.mem_Icc.mpr (abs_le.mp hz))
    exact if_neg hn
  have hc : finitePotentialWeight p s (potentialCutoff R v) = cutoffPotentialWeight p R v := by
    apply Finset.sum_congr rfl
    intro ell hell
    have hz : |ell| ≤ (R : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hell)
    have he : |(ell : ℝ)| ≤ (R : ℝ) := by exact_mod_cast hz
    rw [potentialCutoff, if_pos he]
  simpa only [hc] using fourierWeightedNorm_sampledPotential_le p M h hmesh s
    (potentialCutoff R v) hv y

#print axioms finitePotential_regular
#print axioms sampledPotential_on_modeLift_finset
#print axioms finitePotentialWeight_nonneg
#print axioms fourierWeightedNorm_potential_mode_le
#print axioms fourierWeightedNorm_sampledPotential_le
#print axioms cutoffPotentialWeight_nonneg
#print axioms fourierWeightedNorm_sampledPotential_cutoff_le
end NDEAEvolve.Exp016
