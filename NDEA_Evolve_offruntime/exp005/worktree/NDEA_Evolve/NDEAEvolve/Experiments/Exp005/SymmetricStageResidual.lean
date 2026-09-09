import NDEAEvolve.Experiments.Exp005.MeshWeightedStability

/-!
# Measured stage residuals for the symmetric Cayley scheme

Each factor residual is defined from its supplied source and target states.
An exact ordered identity transfers the three measured residuals to the
full-step discrepancy. Unitarity and resolvent contraction bound the transfer
with constant one, independently of the mesh and generator norms.

The fixed-time corollary assumes an explicit estimate on these actual stage
residuals. It does not derive that estimate from smooth PDE solutions.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

abbrev denominatorHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  operatorOf (cayleyD alpha H)

abbrev numeratorHat {n : ℕ} (H : Mat n) (alpha : ℝ) : E n →L[ℂ] E n :=
  operatorOf (cayleyN alpha H)

/-- The measured residual of one implicit Cayley factor, with no implicit
time-step scaling: denominator times target minus numerator times source. -/
def factorResidual {n : ℕ} (H : Mat n) (alpha : ℝ)
    (source target : E n) : E n :=
  denominatorHat H alpha target - numeratorHat H alpha source

private theorem inverse_mul_numerator {R : Type*} [Ring R]
    (X RX : R) (hLeft : RX * (1 + X) = 1) (hRight : (1 + X) * RX = 1) :
    RX * (1 - X) = (1 - X) * RX := by
  calc
    RX * (1 - X) = RX + RX - RX * (1 + X) := by noncomm_ring
    _ = RX + RX - 1 := by rw [hLeft]
    _ = RX + RX - (1 + X) * RX := by rw [hRight]
    _ = (1 - X) * RX := by noncomm_ring

theorem resolvent_mul_denominatorHat {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    Rhat H alpha * denominatorHat H alpha = 1 := by
  simpa only [Rhat, denominatorHat, operatorOf, map_mul, map_one] using
    congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)
      (cayleyR_mul_cayleyD alpha H hH)

theorem resolvent_mul_numeratorHat {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) :
    Rhat H alpha * numeratorHat H alpha = Chat H alpha := by
  have hLeft : cayleyR alpha H * (1 + skewPart alpha H) = 1 :=
    cayleyR_mul_cayleyD alpha H hH
  have hRight : (1 + skewPart alpha H) * cayleyR alpha H = 1 :=
    cayleyD_mul_cayleyR alpha H hH
  have hm : cayleyR alpha H * cayleyN alpha H = cayley alpha H :=
    inverse_mul_numerator (skewPart alpha H) (cayleyR alpha H) hLeft hRight
  simpa only [Rhat, numeratorHat, Chat, operatorOf, map_mul] using
    congrArg (fun M : Mat n => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M) hm

/-- Exact conversion of the measured implicit-factor residual to a
one-factor state discrepancy. -/
theorem resolvent_factorResidual {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian)
    (source target : E n) :
    Rhat H alpha (factorResidual H alpha source target) =
      target - Chat H alpha source := by
  calc
    Rhat H alpha (factorResidual H alpha source target) =
        (Rhat H alpha * denominatorHat H alpha) target -
          (Rhat H alpha * numeratorHat H alpha) source := by
      simp only [factorResidual, map_sub, ContinuousLinearMap.mul_apply]
    _ = target - Chat H alpha source := by
      rw [resolvent_mul_denominatorHat alpha H hH,
        resolvent_mul_numeratorHat alpha H hH]
      rfl

theorem factorResidual_recurrence {n : ℕ}
    (alpha : ℝ) (H : Mat n) (hH : H.IsHermitian)
    (source target : E n) :
    target = Chat H alpha source + Rhat H alpha (factorResidual H alpha source target) := by
  rw [resolvent_factorResidual alpha H hH source target]
  abel

/-- The sum of the three actual factor-residual norms. Each occurrence uses
the corresponding Cayley parameter k/4, k/2, k/4. -/
def stageResidualBudget {n : ℕ} (dx k : ℝ) (A B : Mat n)
    (source first second target : E n) : ℝ :=
  weightedNorm dx (factorResidual A (k / 4) source first) +
    weightedNorm dx (factorResidual B (k / 2) first second) +
    weightedNorm dx (factorResidual A (k / 4) second target)

theorem stageResidualBudget_nonneg {n : ℕ} (dx k : ℝ) (A B : Mat n)
    (source first second target : E n) :
    0 ≤ stageResidualBudget dx k A B source first second target :=
  add_nonneg (add_nonneg (weightedNorm_nonneg _ _) (weightedNorm_nonneg _ _))
    (weightedNorm_nonneg _ _)

/-- Ordered transfer of all three measured stage residuals. The first
residual passes through both later factors; the middle passes through the
last factor; the last is only resolved by its own inverse denominator. -/
theorem symmetric_stage_residual_identity {n : ℕ}
    (k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (source first second target : E n) :
    target - symmetricStepHat A B k source =
      Chat A (k / 4) (Chat B (k / 2)
        (Rhat A (k / 4) (factorResidual A (k / 4) source first))) +
      Chat A (k / 4) (Rhat B (k / 2) (factorResidual B (k / 2) first second)) +
      Rhat A (k / 4) (factorResidual A (k / 4) second target) := by
  let r1 := factorResidual A (k / 4) source first
  let r2 := factorResidual B (k / 2) first second
  let r3 := factorResidual A (k / 4) second target
  have h1 : first = Chat A (k / 4) source + Rhat A (k / 4) r1 :=
    factorResidual_recurrence (k / 4) A hA source first
  have h2 : second = Chat B (k / 2) first + Rhat B (k / 2) r2 :=
    factorResidual_recurrence (k / 2) B hB first second
  have h3 : target = Chat A (k / 4) second + Rhat A (k / 4) r3 :=
    factorResidual_recurrence (k / 4) A hA second target
  change target - symmetricStepHat A B k source =
    Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1)) +
      Chat A (k / 4) (Rhat B (k / 2) r2) + Rhat A (k / 4) r3
  calc
    target - symmetricStepHat A B k source =
        (Chat A (k / 4)
          (Chat B (k / 2) (Chat A (k / 4) source + Rhat A (k / 4) r1) +
            Rhat B (k / 2) r2) + Rhat A (k / 4) r3) -
          Chat A (k / 4) (Chat B (k / 2) (Chat A (k / 4) source)) := by
      rw [← h1, ← h2, ← h3]
      rfl
    _ = _ := by
      simp only [map_add]
      abel

theorem cayley_weightedNorm_preserved {n : ℕ}
    (dx alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) (x : E n) :
    weightedNorm dx (Chat H alpha x) = weightedNorm dx x := by
  unfold weightedNorm
  rw [cayley_preserves_norm alpha H hH x]

theorem resolvent_weightedNorm_le {n : ℕ}
    (dx alpha : ℝ) (H : Mat n) (hH : H.IsHermitian) (x : E n) :
    weightedNorm dx (Rhat H alpha x) ≤ weightedNorm dx x := by
  unfold weightedNorm
  exact mul_le_mul_of_nonneg_left
    (cayleyR_toEuclideanCLM_apply_norm_le alpha H hH x) (Real.sqrt_nonneg dx)

/-- The measured residuals bound the actual full-step discrepancy with
constant one and no step-size or operator-norm restriction. -/
theorem symmetric_stage_residual_weighted_le {n : ℕ}
    (dx k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (source first second target : E n) :
    weightedNorm dx (target - symmetricStepHat A B k source) ≤
      stageResidualBudget dx k A B source first second target := by
  let r1 := factorResidual A (k / 4) source first
  let r2 := factorResidual B (k / 2) first second
  let r3 := factorResidual A (k / 4) second target
  let d1 := Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1))
  let d2 := Chat A (k / 4) (Rhat B (k / 2) r2)
  let d3 := Rhat A (k / 4) r3
  have h1 : weightedNorm dx d1 ≤ weightedNorm dx r1 := by
    change weightedNorm dx (Chat A (k / 4) (Chat B (k / 2) (Rhat A (k / 4) r1))) ≤ _
    rw [cayley_weightedNorm_preserved dx (k / 4) A hA,
      cayley_weightedNorm_preserved dx (k / 2) B hB]
    exact resolvent_weightedNorm_le dx (k / 4) A hA r1
  have h2 : weightedNorm dx d2 ≤ weightedNorm dx r2 := by
    change weightedNorm dx (Chat A (k / 4) (Rhat B (k / 2) r2)) ≤ _
    rw [cayley_weightedNorm_preserved dx (k / 4) A hA]
    exact resolvent_weightedNorm_le dx (k / 2) B hB r2
  have h3 : weightedNorm dx d3 ≤ weightedNorm dx r3 :=
    resolvent_weightedNorm_le dx (k / 4) A hA r3
  rw [symmetric_stage_residual_identity k A B hA hB]
  change weightedNorm dx (d1 + d2 + d3) ≤
    weightedNorm dx r1 + weightedNorm dx r2 + weightedNorm dx r3
  calc
    _ ≤ weightedNorm dx (d1 + d2) + weightedNorm dx d3 := weightedNorm_add_le _ _ _
    _ ≤ (weightedNorm dx d1 + weightedNorm dx d2) + weightedNorm dx d3 :=
      add_le_add (weightedNorm_add_le dx d1 d2) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

/-- Global a posteriori error certificate for the actual symmetric numerical
trajectory v and supplied reference/stage states. N=0 is included. -/
theorem symmetric_stage_residual_accumulation {n : ℕ}
    (dx k : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v first second : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j)) (N : ℕ) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      ∑ j ∈ Finset.range N,
        stageResidualBudget dx k A B (u j) (first j) (second j) (u (j + 1)) := by
  calc
    _ ≤ weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) :=
      symmetric_weighted_error_accumulation dx k A B hA hB u v hv N
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro j _hj
      exact symmetric_stage_residual_weighted_le dx k A B hA hB
        (u j) (first j) (second j) (u (j + 1))

/-- Conditional space-time error estimate from a mesh-uniform bound on the
sum of the actual stage residuals. Establishing that premise for sampled
smooth PDE solutions is a separate consistency problem. -/
theorem symmetric_stage_residual_fixed_time_error {n : ℕ}
    (dx k T Ct Cs : ℝ) (A B : Mat n) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v first second : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) (hk : 0 ≤ k) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hbudget : ∀ j : ℕ, j < N →
      stageResidualBudget dx k A B (u j) (first j) (second j) (u (j + 1)) ≤
        k * (Ct * k ^ 2 + Cs * dx ^ 2)) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
  apply symmetric_weighted_fixed_time_error dx k T Ct Cs A B hA hB u v hv N
    hk hCt hCs horizon
  intro j hj
  exact (symmetric_stage_residual_weighted_le dx k A B hA hB
    (u j) (first j) (second j) (u (j + 1))).trans (hbudget j hj)

end NDEAEvolve.Exp005

#check @NDEAEvolve.Exp005.symmetric_stage_residual_identity
#check @NDEAEvolve.Exp005.symmetric_stage_residual_fixed_time_error
#print axioms NDEAEvolve.Exp005.resolvent_mul_denominatorHat
#print axioms NDEAEvolve.Exp005.resolvent_mul_numeratorHat
#print axioms NDEAEvolve.Exp005.resolvent_factorResidual
#print axioms NDEAEvolve.Exp005.factorResidual_recurrence
#print axioms NDEAEvolve.Exp005.stageResidualBudget_nonneg
#print axioms NDEAEvolve.Exp005.symmetric_stage_residual_identity
#print axioms NDEAEvolve.Exp005.cayley_weightedNorm_preserved
#print axioms NDEAEvolve.Exp005.resolvent_weightedNorm_le
#print axioms NDEAEvolve.Exp005.symmetric_stage_residual_weighted_le
#print axioms NDEAEvolve.Exp005.symmetric_stage_residual_accumulation
#print axioms NDEAEvolve.Exp005.symmetric_stage_residual_fixed_time_error
