import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Bounded scalar Fourier multipliers followed by summation. Strong joint
continuity and derivatives are derived from ℓ¹ summability of each fixed input.
No summable supremum over a compact family of inputs is assumed. -/
noncomputable section
open scoped BigOperators Topology NNReal
namespace NDEAEvolve.Exp014

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

def scalarSeries (c : ℤ → ℂ) (b : lp (fun _ : ℤ => H) 1) : H :=
  ∑' m, c m • b m

theorem scalarSeries_summable (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : Summable (fun m => c m • b m) := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  apply hb.of_norm_bounded
  intro m
  simpa only [norm_smul, one_mul] using
    mul_le_mul_of_nonneg_right (hc m) (norm_nonneg (b m))

private theorem scalar_identity_norm_le (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c • ContinuousLinearMap.id ℂ H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖c • x‖ ≤ 1 * ‖x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg x)

def scalarSeriesCLM (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    lp (fun _ : ℤ => H) 1 →L[ℂ] H :=
  (lp.tsumCLM (𝕜 := ℂ) (α := ℤ) (E := H)).comp
    (lp.mapCLM 1 (fun m => c m • ContinuousLinearMap.id ℂ H) zero_le_one
      (fun m => scalar_identity_norm_le (c m) (hc m)))

theorem scalarSeriesCLM_apply (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : scalarSeriesCLM c hc b = scalarSeries c b := rfl

theorem scalarSeriesCLM_norm_le (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) :
    ‖scalarSeriesCLM (H := H) c hc‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have h1 : ‖lp.tsumCLM (𝕜 := ℂ) (α := ℤ) (E := H)‖ ≤ 1 := lp.norm_tsumCLM_le
  have h2 := lp.norm_mapCLM_le 1 (fun m : ℤ => c m • ContinuousLinearMap.id ℂ H)
    zero_le_one (fun m => scalar_identity_norm_le (c m) (hc m))
  simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one

theorem scalarSeries_norm_le (c : ℤ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1)
    (b : lp (fun _ : ℤ => H) 1) : ‖scalarSeries c b‖ ≤ ‖b‖ := by
  change ‖scalarSeriesCLM c hc b‖ ≤ ‖b‖
  simpa only [one_mul] using
    (scalarSeriesCLM (H := H) c hc).le_of_opNorm_le
      (scalarSeriesCLM_norm_le (H := H) c hc) b

theorem scalarSeries_continuous {P : Type*} [TopologicalSpace P]
    (c : P → ℤ → ℂ) (hc : ∀ p m, ‖c p m‖ ≤ 1)
    (hcont : ∀ m, Continuous (fun p => c p m)) (b : lp (fun _ : ℤ => H) 1) :
    Continuous (fun p => scalarSeries (c p) b) := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  exact continuous_tsum (fun m => (hcont m).smul continuous_const) hb
    (fun m p => by simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (hc p m) (norm_nonneg (b m)))

theorem scalarSeries_joint_continuous {P : Type*} [TopologicalSpace P]
    (c : P → ℤ → ℂ) (hc : ∀ p m, ‖c p m‖ ≤ 1)
    (hcont : ∀ m, Continuous (fun p => c p m)) :
    Continuous (fun q : P × lp (fun _ : ℤ => H) 1 => scalarSeries (c q.1) q.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro p
    change LipschitzWith 1 (scalarSeriesCLM (H := H) (c p) (hc p))
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := (1 : ℝ≥0))
      (scalarSeriesCLM_norm_le (H := H) (c p) (hc p))
  · exact scalarSeries_continuous c hc hcont

theorem scalarSeries_hasDerivAt (c c' : ℝ → ℤ → ℂ)
    (hc : ∀ t m, ‖c t m‖ ≤ 1) (hc' : ∀ t m, ‖c' t m‖ ≤ 1)
    (hd : ∀ t m, HasDerivAt (fun s => c s m) (c' t m) t)
    (b : lp (fun _ : ℤ => H) 1) (t : ℝ) :
    HasDerivAt (fun s => scalarSeries (c s) b) (scalarSeries (c' t) b) t := by
  have hb : Summable (fun m : ℤ => ‖b m‖) := by simpa using b.2.summable
  exact hasDerivAt_tsum hb (fun m s => (hd s m).smul_const (b m))
    (fun m s => by simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (hc' s m) (norm_nonneg (b m)))
    (scalarSeries_summable (c 0) (hc 0) b) t

end NDEAEvolve.Exp014
