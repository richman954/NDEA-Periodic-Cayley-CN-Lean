import NDEAEvolve.Experiments.Exp004.SymmetricCayleyGlobal

/-!
# Mesh-weighted stability and measured trajectory defects

The weight is the square root of a real mesh parameter, multiplying the
existing Euclidean norm. Stability and accumulation are algebraic consequences
of the symmetric step's unconditional unitarity. No generator-norm bound or
small-step hypothesis is used here.

The fixed-time estimate takes a bound on the actual trajectory defect as an
explicit premise. It does not derive that premise from a differential equation.
-/

noncomputable section

open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

def weightedNorm {n : ℕ} (dx : ℝ) (x : E n) : ℝ :=
  Real.sqrt dx * ‖x‖

theorem weightedNorm_nonneg {n : ℕ} (dx : ℝ) (x : E n) :
    0 ≤ weightedNorm dx x :=
  mul_nonneg (Real.sqrt_nonneg dx) (norm_nonneg x)

@[simp]
theorem weightedNorm_zero (dx : ℝ) (n : ℕ) :
    weightedNorm dx (0 : E n) = 0 := by
  simp [weightedNorm]

@[simp]
theorem weightedNorm_neg {n : ℕ} (dx : ℝ) (x : E n) :
    weightedNorm dx (-x) = weightedNorm dx x := by
  simp [weightedNorm]

theorem weightedNorm_sub_rev {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x - y) = weightedNorm dx (y - x) := by
  unfold weightedNorm
  rw [norm_sub_rev]

theorem weightedNorm_add_le {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x + y) ≤ weightedNorm dx x + weightedNorm dx y := by
  unfold weightedNorm
  calc
    Real.sqrt dx * ‖x + y‖ ≤ Real.sqrt dx * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le x y) (Real.sqrt_nonneg dx)
    _ = Real.sqrt dx * ‖x‖ + Real.sqrt dx * ‖y‖ := by ring

theorem weightedNorm_sub_le {n : ℕ} (dx : ℝ) (x y : E n) :
    weightedNorm dx (x - y) ≤ weightedNorm dx x + weightedNorm dx y := by
  simpa only [sub_eq_add_neg, weightedNorm_neg] using
    weightedNorm_add_le dx x (-y)

theorem weightedNorm_smul {n : ℕ} (dx : ℝ) (c : ℂ) (x : E n) :
    weightedNorm dx (c • x) = ‖c‖ * weightedNorm dx x := by
  simp only [weightedNorm, norm_smul]
  ring

theorem weightedNorm_real_smul {n : ℕ} (dx k : ℝ) (x : E n) :
    weightedNorm dx (k • x) = |k| * weightedNorm dx x := by
  simp only [weightedNorm, norm_smul, Real.norm_eq_abs]
  ring

theorem weightedNorm_eq_zero_iff {n : ℕ} (dx : ℝ) (hdx : 0 < dx) (x : E n) :
    weightedNorm dx x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsqrt : Real.sqrt dx ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdx)
    have hx : ‖x‖ = 0 := (mul_eq_zero.mp h).resolve_left hsqrt
    exact norm_eq_zero.mp hx
  · rintro rfl
    exact weightedNorm_zero dx n

/-- The weighted norm is preserved for every real symmetric time step and
every finite dimension. The mesh parameter need not bound the generators. -/
theorem symmetricStepHat_weightedNorm_preserved {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (x : E n) :
    weightedNorm dx (symmetricStepHat A B k x) = weightedNorm dx x := by
  unfold weightedNorm
  rw [ContinuousLinearMap.norm_map_of_mem_unitary
    (symmetricStepHat_mem_unitary k A B hA hB) x]

theorem symmetricStepHat_weighted_distance_preserved {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (x y : E n) :
    weightedNorm dx
        (symmetricStepHat A B k x - symmetricStepHat A B k y) =
      weightedNorm dx (x - y) := by
  rw [← map_sub]
  exact symmetricStepHat_weightedNorm_preserved dx k A B hA hB (x - y)

/-- The discrepancy of a supplied reference trajectory from one actual
symmetric numerical step, with its sign and argument order fixed. -/
def trajectoryDefect {n : ℕ} (A B : Mat n) (k : ℝ)
    (u : ℕ → E n) (j : ℕ) : E n :=
  u (j + 1) - symmetricStepHat A B k (u j)

theorem trajectoryDefect_recurrence {n : ℕ} (A B : Mat n) (k : ℝ)
    (u : ℕ → E n) (j : ℕ) :
    u (j + 1) = symmetricStepHat A B k (u j) + trajectoryDefect A B k u j := by
  unfold trajectoryDefect
  abel

/-- Actual trajectory defects accumulate without amplification in the
mesh-weighted norm. This theorem includes the empty sum at N=0. -/
theorem symmetric_weighted_error_accumulation {n : ℕ}
    (dx k : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) :
    weightedNorm dx (u N - v N) ≤
      weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [trajectoryDefect_recurrence A B k u N, hv N]
      calc
        weightedNorm dx
            (symmetricStepHat A B k (u N) + trajectoryDefect A B k u N -
              symmetricStepHat A B k (v N)) =
            weightedNorm dx
              ((symmetricStepHat A B k (u N) - symmetricStepHat A B k (v N)) +
                trajectoryDefect A B k u N) := by
          congr 1
          abel
        _ ≤ weightedNorm dx
              (symmetricStepHat A B k (u N) - symmetricStepHat A B k (v N)) +
            weightedNorm dx (trajectoryDefect A B k u N) :=
          weightedNorm_add_le _ _ _
        _ = weightedNorm dx (u N - v N) +
            weightedNorm dx (trajectoryDefect A B k u N) := by
          rw [symmetricStepHat_weighted_distance_preserved dx k A B hA hB]
        _ ≤ (weightedNorm dx (u 0 - v 0) +
              ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j)) +
            weightedNorm dx (trajectoryDefect A B k u N) :=
          add_le_add ih (le_refl _)
        _ = weightedNorm dx (u 0 - v 0) +
              ∑ j ∈ Finset.range (N + 1),
                weightedNorm dx (trajectoryDefect A B k u j) := by
          rw [Finset.sum_range_succ]
          ring

/-- A supplied space-time residual estimate yields a fixed-time error
certificate for the actual symmetric recurrence. Uniformity across meshes
requires the constants in this explicit premise to be uniform. -/
theorem symmetric_weighted_fixed_time_error {n : ℕ}
    (dx k T Ct Cs : ℝ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u v : ℕ → E n)
    (hv : ∀ j : ℕ, v (j + 1) = symmetricStepHat A B k (v j))
    (N : ℕ) (hk : 0 ≤ k) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : (N : ℝ) * k ≤ T)
    (hdefect : ∀ j : ℕ, j < N →
      weightedNorm dx (trajectoryDefect A B k u j) ≤
        k * (Ct * k ^ 2 + Cs * dx ^ 2)) :
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
      T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
  have hrate : 0 ≤ Ct * k ^ 2 + Cs * dx ^ 2 :=
    add_nonneg (mul_nonneg hCt (sq_nonneg k))
      (mul_nonneg hCs (sq_nonneg dx))
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  calc
    weightedNorm dx (u N - v N) ≤ weightedNorm dx (u 0 - v 0) +
        ∑ j ∈ Finset.range N, weightedNorm dx (trajectoryDefect A B k u j) :=
      symmetric_weighted_error_accumulation dx k A B hA hB u v hv N
    _ ≤ weightedNorm dx (u 0 - v 0) +
        ∑ _j ∈ Finset.range N, k * (Ct * k ^ 2 + Cs * dx ^ 2) := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro j hj
      exact hdefect j (Finset.mem_range.mp hj)
    _ = weightedNorm dx (u 0 - v 0) +
        (N : ℝ) * (k * (Ct * k ^ 2 + Cs * dx ^ 2)) := by simp
    _ ≤ weightedNorm dx (u 0 - v 0) +
        T * (Ct * k ^ 2 + Cs * dx ^ 2) := by
      apply add_le_add (le_refl _)
      rw [← mul_assoc]
      exact mul_le_mul horizon (le_refl _) hrate hT

/-- A uniform pointwise residual bound becomes a weighted Euclidean bound
depending on the physical length, with no dimension factor. Zero dimension
is included when the cardinality/mesh identity forces L=0. -/
theorem weightedNorm_of_pointwise_bound {n : ℕ}
    (dx L R : ℝ) (hdx : 0 ≤ dx) (hL : 0 ≤ L)
    (hcard : (n : ℝ) * dx = L) (r : Fin n → ℂ)
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) :
    weightedNorm dx (WithLp.toLp 2 r) ≤ Real.sqrt L * R := by
  have hsquared : weightedNorm dx (WithLp.toLp 2 r) ^ 2 ≤ L * R ^ 2 := by
    rw [weightedNorm, mul_pow, Real.sq_sqrt hdx, EuclideanSpace.norm_sq_eq]
    change dx * ∑ i : Fin n, ‖r i‖ ^ 2 ≤ L * R ^ 2
    calc
      dx * ∑ i : Fin n, ‖r i‖ ^ 2 ≤ dx * ∑ _i : Fin n, R ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hdx
        apply Finset.sum_le_sum
        intro i _hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hr i) 2
      _ = dx * ((n : ℝ) * R ^ 2) := by simp
      _ = L * R ^ 2 := by rw [← hcard]; ring
  have hright : (Real.sqrt L * R) ^ 2 = L * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL]
  have hleftNonneg := weightedNorm_nonneg dx (WithLp.toLp 2 r)
  have hrightNonneg := mul_nonneg (Real.sqrt_nonneg L) hR
  nlinarith

end NDEAEvolve.Exp005

#print axioms NDEAEvolve.Exp005.weightedNorm_nonneg
#print axioms NDEAEvolve.Exp005.weightedNorm_zero
#print axioms NDEAEvolve.Exp005.weightedNorm_neg
#print axioms NDEAEvolve.Exp005.weightedNorm_sub_rev
#print axioms NDEAEvolve.Exp005.weightedNorm_add_le
#print axioms NDEAEvolve.Exp005.weightedNorm_sub_le
#print axioms NDEAEvolve.Exp005.weightedNorm_smul
#print axioms NDEAEvolve.Exp005.weightedNorm_real_smul
#print axioms NDEAEvolve.Exp005.weightedNorm_eq_zero_iff
#print axioms NDEAEvolve.Exp005.symmetricStepHat_weightedNorm_preserved
#print axioms NDEAEvolve.Exp005.symmetricStepHat_weighted_distance_preserved
#print axioms NDEAEvolve.Exp005.trajectoryDefect_recurrence
#print axioms NDEAEvolve.Exp005.symmetric_weighted_error_accumulation
#print axioms NDEAEvolve.Exp005.symmetric_weighted_fixed_time_error
#print axioms NDEAEvolve.Exp005.weightedNorm_of_pointwise_bound
