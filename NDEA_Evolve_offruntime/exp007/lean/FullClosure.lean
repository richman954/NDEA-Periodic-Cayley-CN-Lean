import ReducedClosure
import ContinuumSpinor
import SpinorGrid

/-! Actual periodic spinor-grid error, with arbitrary numerical initialization. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007
open SpinorGrid

theorem reference_power (v0 : E 2) (k : ℝ) (N : ℕ) :
    (exactStepHat (A0+B) (k/2)^N) v0 = v v0 ((N : ℝ)*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, v_exact_step]
    congr 1
    push_cast
    ring

def gridError (n : ℕ) (h k : ℝ) (N : ℕ) (initial : Vec (Grid n)) (v0 : E 2) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Z X ^ N) initial -
    liftCLM n h (v v0 ((N : ℝ)*k))‖

def initialError (n : ℕ) (h : ℝ) (initial : Vec (Grid n)) (v0 : E 2) : ℝ :=
  Real.sqrt h * ‖initial - liftCLM n h v0‖

/-- The terminal time is Nk≤T. The initial numerical state may contain any
grid modes; its full weighted initial error is retained. -/
theorem concrete_noncommuting_grid_error (n : ℕ) (h k T : ℝ) (N : ℕ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (initial : Vec (Grid n)) (v0 : E 2) :
    gridError n h k N initial v0 ≤ initialError n h initial v0 +
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
  let S := symmetric n h k Z X
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((S^N) initial) ((S^N) (liftCLM n h v0))
    (liftCLM n h (v v0 ((N : ℝ)*k)))
  have hstable : ‖(S^N) initial - (S^N) (liftCLM n h v0)‖ =
      ‖initial - liftCLM n h v0‖ := by
    rw [← map_sub]
    exact symmetric_pow_norm n h k Z X Z_isHermitian X_isHermitian N _
  have hexact : Real.sqrt h * ‖(S^N) (liftCLM n h v0) -
      liftCLM n h (v v0 ((N : ℝ)*k))‖ ≤
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
    rw [symmetric_pow_weighted_error n h k Z X Z_isHermitian X_isHermitian
      hh.le hmesh N v0 (v v0 ((N : ℝ)*k)), ← reference_power]
    have he := reduced_power_error_apply h k T N hh hhsmall hk hksmall horizon v0
    calc
      _ ≤ Real.sqrt (2*Real.pi)*(T*(27000*k^2+h^2/8)*‖v0‖) :=
        mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
      _ = _ := by ring
  change Real.sqrt h * _ ≤ Real.sqrt h * _ + _
  rw [hstable] at htri
  have hb := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg h)
  rw [mul_add] at hb
  exact hb.trans (add_le_add (le_refl _) hexact)

theorem concrete_noncommuting_exact_initial_error (n : ℕ) (h k T : ℝ) (N : ℕ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6)
    (horizon : (N : ℝ)*k ≤ T) (v0 : E 2) :
    gridError n h k N (liftCLM n h v0) v0 ≤
      Real.sqrt (2*Real.pi)*T*(27000*k^2+h^2/8)*‖v0‖ := by
  simpa [initialError] using concrete_noncommuting_grid_error n h k T N hmesh
    hh hhsmall hk hksmall horizon (liftCLM n h v0) v0

/-- Scalar weighted errors converge even though each mesh has a different
finite-dimensional state space. -/
theorem concrete_noncommuting_mesh_error_tendsto_zero
    (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ) (v0 : E 2)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hmesh : ∀ q, ((n q+1 : ℕ) : ℝ)*h q = 2*Real.pi)
    (hh : ∀ q, 0 < h q) (hhsmall : ∀ q, h q ≤ 1)
    (hk : ∀ q, 0 ≤ k q) (hksmall : ∀ q, k q ≤ 1/6)
    (horizon : ∀ q, (N q : ℝ)*k q ≤ T)
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hinitial : Filter.Tendsto (fun q => initialError (n q) (h q) (initial q) v0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => gridError (n q) (h q) (k q) (N q) (initial q) v0)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => by unfold gridError; positivity)
  · intro q
    exact concrete_noncommuting_grid_error (n q) (h q) (k q) T (N q)
      (hmesh q) (hh q) (hhsmall q) (hk q) (hksmall q) (horizon q) (initial q) v0
  · have hrate := ((hk_limit.pow 2).const_mul 27000).add ((hh_limit.pow 2).div_const 8)
    have hb := hinitial.add ((hrate.const_mul (Real.sqrt (2*Real.pi)*T)).mul_const ‖v0‖)
    simpa using hb

#print axioms reference_power
#print axioms concrete_noncommuting_grid_error
#print axioms concrete_noncommuting_mesh_error_tendsto_zero
end NDEAEvolve.Exp007
