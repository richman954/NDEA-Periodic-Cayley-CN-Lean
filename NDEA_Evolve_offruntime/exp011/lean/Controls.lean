import UniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact index, initialization, inverse-norm, and infinite-support controls
for the explicit reconstructed fields. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011.Controls

theorem spaceIndex_at_zero (n : ℕ) (h : ℝ) : (spaceIndex n h 0).val=0 := by
  simp [spaceIndex]

theorem spaceIndex_at_right_endpoint (n : ℕ) (h : ℝ) (hh : 0<h) :
    (spaceIndex n h (((n+1:ℕ):ℝ)*h)).val=n := by
  change min ⌊(((n+1:ℕ):ℝ)*h)/h⌋₊ n=n
  rw [mul_div_cancel_right₀ _ hh.ne', Nat.floor_natCast,
    min_eq_right (Nat.le_succ n)]

theorem timeIndex_at_zero (N : ℕ) (k : ℝ) : timeIndex N k 0=0 := by
  simp [timeIndex]

theorem timeIndex_at_final_time (N : ℕ) (k : ℝ) (hk : 0<k) :
    timeIndex N k ((N:ℝ)*k)=N := by
  simp [timeIndex, mul_div_cancel_right₀ _ hk.ne']

theorem gridState_initial (n : ℕ) (h k : ℝ) (a : ℤ → E 2) :
    gridState n h k a 0=sampleSolution n h (infiniteSolution a) 0 := by
  simp [gridState]

theorem reconstruction_at_final_time (n : ℕ) (h k : ℝ) (N : ℕ)
    (a : ℤ → E 2) (x : ℝ) (hk : 0<k) :
    reconstruction n h k N a ((N:ℝ)*k) x =
      nodeValue n (gridState n h k a N) (spaceIndex n h x) := by
  rw [reconstruction, timeIndex_at_final_time N k hk]

def nodeSpike (n : ℕ) (j : Fin (n+1)) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => if p.1=j then v p.2 else 0)

theorem nodeValue_spike (n : ℕ) (j : Fin (n+1)) (v : E 2) :
    nodeValue n (nodeSpike n j v) j=v := by
  ext b
  simp [nodeValue, nodeSpike]

theorem nodeSpike_norm (n : ℕ) (j : Fin (n+1)) (v : E 2) :
    ‖nodeSpike n j v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [nodeSpike, Fintype.sum_prod_type, apply_ite]

/-- A single-node error defeats a purported pointwise bound by the weighted
grid norm without the necessary inverse square-root mesh factor. -/
theorem weighted_grid_norm_alone_does_not_bound_node (n : ℕ) (h : ℝ)
    (hh : 0<h) (hsmall : h<1) (j : Fin (n+1)) :
    Real.sqrt h*‖nodeSpike n j Exp007.Controls.initialSpinor‖ <
      ‖nodeValue n (nodeSpike n j Exp007.Controls.initialSpinor) j‖ := by
  rw [nodeValue_spike, nodeSpike_norm, Exp007.Controls.initialSpinor_norm, mul_one]
  nlinarith [Real.sq_sqrt hh.le, Real.sqrt_nonneg h]

def regularCoefficients (m : ℤ) : E 2 :=
  ((1/2 : ℂ)^Encodable.encode m / (frequencyWeight 2 m : ℂ)) •
    Exp007.Controls.initialSpinor

theorem regular_coefficient_norm (m : ℤ) :
    ‖regularCoefficients m‖=(1/2 : ℝ)^Encodable.encode m/frequencyWeight 2 m := by
  simp [regularCoefficients, norm_smul, norm_pow, Exp007.Controls.initialSpinor_norm,
    Real.norm_eq_abs, abs_of_nonneg (frequencyWeight_nonneg 2 m)]

theorem regular_weighted_norm (m : ℤ) :
    frequencyWeight 2 m*‖regularCoefficients m‖=(1/2 : ℝ)^Encodable.encode m := by
  rw [regular_coefficient_norm]
  exact mul_div_cancel₀ _ (frequencyWeight_two_pos m).ne'

theorem coefficients_regular : Regular regularCoefficients := by
  change Summable (fun m : ℤ => frequencyWeight 2 m*‖regularCoefficients m‖)
  simp only [regular_weighted_norm]
  exact summable_geometric_two_encode

theorem regular_coefficient_nonzero (m : ℤ) : regularCoefficients m≠0 := by
  apply norm_ne_zero_iff.mp
  rw [regular_coefficient_norm]
  have hw := frequencyWeight_two_pos m
  positivity

theorem regular_coefficients_infinite_support : (Function.support regularCoefficients).Infinite := by
  have hs : Function.support regularCoefficients=Set.univ := by
    ext m
    simp [Function.mem_support, regular_coefficient_nonzero]
  rw [hs]
  exact Set.infinite_univ

theorem infinite_support_uniform_classical_example :
    (Function.support regularCoefficients).Infinite ∧
    IsClassicalPeriodicSolution (infiniteSolution regularCoefficients) ∧
    TendstoUniformlyOn
      (fun q (p : ℝ × ℝ) => scheduledReconstruction q regularCoefficients p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution regularCoefficients p.1 p.2)
      Filter.atTop spaceTimeDomain :=
  ⟨regular_coefficients_infinite_support,
    classical_uniform_reconstruction regularCoefficients coefficients_regular⟩

end NDEAEvolve.Exp011.Controls
