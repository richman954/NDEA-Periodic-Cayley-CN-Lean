import ContinuumModes
import Orthogonality

/-! Full-grid error for a fixed finite Fourier spectrum. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008
open FourierGrid

def coefficientNorm (S : Finset ℤ) (a : ℤ → E 2) : ℝ :=
  Real.sqrt (∑ m ∈ S, ‖a m‖^2)

theorem coefficientNorm_nonneg (S : Finset ℤ) (a : ℤ → E 2) :
    0 ≤ coefficientNorm S a := Real.sqrt_nonneg _

theorem coefficientNorm_bound (S : Finset ℤ) (a b : ℤ → E 2) (c : ℝ)
    (hc : 0 ≤ c) (hb : ∀ m ∈ S, ‖b m‖ ≤ c*‖a m‖) :
    coefficientNorm S b ≤ c*coefficientNorm S a := by
  have ha : 0 ≤ ∑ m ∈ S, ‖a m‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ m ∈ S, ‖b m‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (coefficientNorm_nonneg S b)
    (mul_nonneg hc (coefficientNorm_nonneg S a))).mp
  unfold coefficientNorm
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb0]
  calc
    _ ≤ ∑ m ∈ S, (c*‖a m‖)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (norm_nonneg _) (hb m hm) 2
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

@[simp] theorem coefficientNorm_orbit (S : Finset ℤ) (a : ℤ → E 2) (t : ℝ) :
    coefficientNorm S (fun m => modeOrbit m t (a m)) = coefficientNorm S a := by
  simp [coefficientNorm]

theorem modeOrbit_power (m : ℤ) (v : E 2) (k : ℝ) (N : ℕ) :
    (exactStepHat (modeGenerator m) (k/2)^N) v = modeOrbit m ((N:ℝ)*k) v := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, modeOrbit_exact_step]
    congr 1
    push_cast
    ring

theorem superpositionLift_sub (n : ℕ) (h : ℝ) (S : Finset ℤ) (a b : ℤ → E 2) :
    superpositionLift n h S a - superpositionLift n h S b =
      superpositionLift n h S (fun m => a m-b m) := by
  simp only [superpositionLift, map_sub, Finset.sum_sub_distrib]

theorem superposition_is_sampled_solution (n : ℕ) (h : ℝ) (S : Finset ℤ)
    (a : ℤ → E 2) (t : ℝ) (p : Grid n) :
    superpositionLift n h S (fun m => modeOrbit m t (a m)) p =
      finiteSolution S a t ((p.1.val:ℝ)*h) p.2 := by
  simp [superpositionLift, modeLiftCLM, modeLiftLinear, modeLift,
    finiteSolution, modeSolution, mul_assoc]

theorem frequency_power_error_apply (M : ℕ) (m : ℤ) (h k T : ℝ) (N : ℕ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) (v : E 2) :
    ‖(symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) v-
      modeOrbit m ((N:ℝ)*k) v‖ ≤ T*(Ct M*k^2+Cs M*h^2)*‖v‖ := by
  rw [← modeOrbit_power m v k N]
  change ‖(symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) v-
    (exactStepHat (Exp007.A ((m:ℝ)^2)+Exp007.B) (k/2)^N) v‖ ≤ _
  rw [← ContinuousLinearMap.sub_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (frequency_power_error M m h k T N hM hm hh hMh hk hstep horizon) (norm_nonneg v))

def finiteGridError (n : ℕ) (h k : ℝ) (N : ℕ) (S : Finset ℤ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖(symmetric n h k Exp007.Z Exp007.X ^ N) initial-
    superpositionLift n h S (fun m => modeOrbit m ((N:ℝ)*k) (a m))‖

def finiteInitialError (n : ℕ) (h : ℝ) (S : Finset ℤ)
    (a : ℤ → E 2) (initial : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖initial-superpositionLift n h S a‖

theorem finite_superposition_exact_initial_error (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hM : 1 ≤ M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    finiteGridError n h k N S a (superpositionLift n h S a) ≤
      Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let b := fun m => (symmetricStepHat (Exp007.A (modeSymbol m h)) Exp007.B k ^ N) (a m)-
    modeOrbit m ((N:ℝ)*k) (a m)
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) hk).trans horizon
  have hc : 0 ≤ T*(Ct M*k^2+Cs M*h^2) :=
    mul_nonneg hT (add_nonneg (mul_nonneg (Ct_nonneg M) (sq_nonneg k))
      (mul_nonneg (Cs_nonneg M) (sq_nonneg h)))
  have hb : coefficientNorm S b ≤ T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a :=
    coefficientNorm_bound S a b _ hc fun m hm =>
      frequency_power_error_apply M m h k T N hM (hS m hm) hh hMh hk hstep horizon (a m)
  unfold finiteGridError
  rw [symmetric_pow_superposition n h k Exp007.Z Exp007.X
    Exp007.Z_isHermitian Exp007.X_isHermitian hmesh N S a, superpositionLift_sub]
  change Real.sqrt h*‖superpositionLift n h S b‖ ≤ _
  rw [band_superposition_weighted_norm M n h hh.le hmesh S hband hS b]
  change Real.sqrt (2*Real.pi)*coefficientNorm S b ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi)*(T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The numerical initial state may contain any grid frequencies; retain its entire error. -/
theorem finite_superposition_grid_error (M n : ℕ) (h k T : ℝ) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2) (initial : Vec (Grid n))
    (hM : 1 ≤ M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0 < h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0 ≤ k)
    (hstep : 2*k*((M:ℝ)^2+2) ≤ 1) (horizon : (N:ℝ)*k ≤ T) :
    finiteGridError n h k N S a initial ≤ finiteInitialError n h S a initial+
      Real.sqrt (2*Real.pi)*T*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let G := symmetric n h k Exp007.Z Exp007.X
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((G^N) initial) ((G^N) (superpositionLift n h S a))
    (superpositionLift n h S (fun m => modeOrbit m ((N:ℝ)*k) (a m)))
  have hs : ‖(G^N) initial-(G^N) (superpositionLift n h S a)‖ =
      ‖initial-superpositionLift n h S a‖ := by
    rw [← map_sub]
    exact symmetric_pow_norm n h k Exp007.Z Exp007.X
      Exp007.Z_isHermitian Exp007.X_isHermitian N _
  rw [hs] at htri
  have ht := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg h)
  rw [mul_add] at ht
  exact ht.trans (add_le_add (le_refl _) (finite_superposition_exact_initial_error
    M n h k T N S a hM hband hS hmesh hh hMh hk hstep horizon))

/-- The cutoff and spectrum stay fixed while grid dimensions may vary. -/
theorem finite_superposition_mesh_error_tendsto_zero
    (M : ℕ) (S : Finset ℤ) (a : ℤ → E 2) (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (initial : (q : ℕ) → Vec (Grid (n q)))
    (hM : 1 ≤ M) (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hband : ∀ q, 2*M<n q+1)
    (hmesh : ∀ q, ((n q+1:ℕ):ℝ)*h q=2*Real.pi)
    (hh : ∀ q, 0<h q) (hMh : ∀ q, (M:ℝ)*h q≤1)
    (hk : ∀ q, 0≤k q) (hstep : ∀ q, 2*k q*((M:ℝ)^2+2)≤1)
    (horizon : ∀ q, (N q:ℝ)*k q≤T)
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hi_limit : Filter.Tendsto (fun q => finiteInitialError (n q) (h q) S a (initial q))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun q => finiteGridError (n q) (h q) (k q) (N q) S a (initial q))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => by unfold finiteGridError; positivity)
  · intro q
    exact finite_superposition_grid_error M (n q) (h q) (k q) T (N q) S a (initial q)
      hM (hband q) hS (hmesh q) (hh q) (hMh q) (hk q) (hstep q) (horizon q)
  · have hr := ((hk_limit.pow 2).const_mul (Ct M)).add ((hh_limit.pow 2).const_mul (Cs M))
    have hb := hi_limit.add ((hr.const_mul (Real.sqrt (2*Real.pi)*T)).mul_const (coefficientNorm S a))
    simpa using hb

end NDEAEvolve.Exp008
