import InfiniteReference

/-! Actual full-grid error against an absolutely summable infinite Fourier reference. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009

def infiniteGridError (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial -
    infiniteGrid n h a ((N:ℝ)*k)‖

def infiniteInitialError (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial - infiniteGrid n h a 0‖

theorem infiniteGridError_nonneg (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : 0 ≤ infiniteGridError n h k N a initial := by
  unfold infiniteGridError
  positivity

theorem infiniteInitialError_nonneg (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) : 0 ≤ infiniteInitialError n h a initial := by
  unfold infiniteInitialError
  positivity

theorem infinite_exact_initial_error (n : ℕ) (h : ℝ) (a : ℤ → E 2) :
    infiniteInitialError n h a (infiniteGrid n h a 0) = 0 := by
  simp [infiniteInitialError]

theorem zero_steps_retain_full_initial_error (n : ℕ) (h k : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) :
    infiniteGridError n h k 0 a initial = infiniteInitialError n h a initial := by
  simp [infiniteGridError, infiniteInitialError]

theorem finite_initial_error_le_full (M n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (initial : Vec (Grid n)) (ha : Summable fun m => ‖a m‖)
    (hh : 0 < h) (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    finiteInitialError n h (band M) a initial ≤
      infiniteInitialError n h a initial + Real.sqrt (2*Real.pi)*tail M a := by
  have hb := infiniteGrid_tail_bound M n h a 0 ha hh hmesh
  simp only [modeOrbit_initial] at hb
  have ht := mul_le_mul_of_nonneg_left
    (norm_sub_le_norm_sub_add_norm_sub initial (infiniteGrid n h a 0)
      (superpositionLift n h (band M) a)) (Real.sqrt_nonneg h)
  rw [mul_add] at ht
  exact ht.trans (add_le_add (le_refl _) hb)

theorem infinite_grid_error_bound (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) (ha : Summable fun m => ‖a m‖)
    (hM : 1 ≤ M) (hband : 2*M<n+1)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k)
    (hstep : 2*k*((M:ℝ)^2+2)≤1) (horizon : (N:ℝ)*k≤T) :
    infiniteGridError n h k N a initial ≤ infiniteInitialError n h a initial +
      Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*mass a + 2*tail M a) := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  have hcost : 0 ≤ Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2) := by
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hT)
    exact add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
      (mul_nonneg (Cs_nonneg M) (sq_nonneg h))
  have ht := mul_le_mul_of_nonneg_left
    (norm_sub_le_norm_sub_add_norm_sub
      ((symmetric n h k Exp007.Z Exp007.X ^ N) initial)
      (superpositionLift n h (band M) (fun m => modeOrbit m ((N:ℝ)*k) (a m)))
      (infiniteGrid n h a ((N:ℝ)*k))) (Real.sqrt_nonneg h)
  rw [mul_add, norm_sub_rev (superpositionLift _ _ _ _)] at ht
  have htail := infiniteGrid_tail_bound M n h a ((N:ℝ)*k) ha hh hmesh
  have hfinite := finite_superposition_grid_error M n h k T N (band M) a initial
    hM hband (band_frequency_bound M) hmesh hh hMh hk hstep horizon
  have hi := finite_initial_error_le_full M n h a initial ha hh hmesh
  have hc := mul_le_mul_of_nonneg_left (coefficientNorm_band_le_mass M a ha) hcost
  change infiniteGridError n h k N a initial ≤ _ at ht
  change Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm (band M) a ≤
    Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*mass a at hc
  calc
    _ ≤ finiteGridError n h k N (band M) a initial +
        Real.sqrt (2*Real.pi)*tail M a := ht.trans (add_le_add (le_refl _) htail)
    _ ≤ (infiniteInitialError n h a initial + Real.sqrt (2*Real.pi)*tail M a) +
        Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*mass a +
        Real.sqrt (2*Real.pi)*tail M a :=
      add_le_add (hfinite.trans (add_le_add hi hc)) (le_refl _)
    _ = _ := by ring

theorem infinite_mesh_error_tendsto_zero
    (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖)
    (M n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hM : ∀ q, 1≤M q) (hband : ∀ q, 2*M q<n q+1)
    (hmesh : ∀ q, ((n q+1:ℕ):ℝ)*h q=2*Real.pi)
    (hh : ∀ q, 0<h q) (hMh : ∀ q, (M q:ℝ)*h q≤1)
    (hk : ∀ q, 0≤k q) (hstep : ∀ q, 2*k q*((M q:ℝ)^2+2)≤1)
    (horizon : ∀ q, (N q:ℝ)*k q≤T)
    (hM_limit : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hcost_limit : Filter.Tendsto (fun q => Ct (M q)*(k q)^2+Cs (M q)*(h q)^2)
      Filter.atTop (nhds 0))
    (hi_limit : Filter.Tendsto (fun q => infiniteInitialError (n q) (h q) a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => infiniteGridError (n q) (h q) (k q) (N q) a (initial q))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => infiniteGridError_nonneg _ _ _ _ _ _)
  · intro q
    exact infinite_grid_error_bound (M q) (n q) (h q) (k q) T (N q) a (initial q) ha
      (hM q) (hband q) (hmesh q) (hh q) (hMh q) (hk q) (hstep q) (horizon q)
  · have htail := (tail_tendsto_zero a ha).comp hM_limit
    have hb := hi_limit.add
      ((((hcost_limit.const_mul T).mul_const (mass a)).add (htail.const_mul 2)).const_mul
        (Real.sqrt (2*Real.pi)))
    simpa using hb

end NDEAEvolve.Exp009
