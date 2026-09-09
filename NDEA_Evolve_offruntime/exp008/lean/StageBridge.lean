import SuperpositionClosure

/-! The actual full-grid implicit-factor residuals decompose by frequency.
Parseval aggregates the final residual in coefficient ℓ²; the first two
auxiliary states are the actual numerical stages and have zero residual. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
open NDEAEvolve.Exp007 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp008
open FourierGrid

theorem gridFactorResidual_modeLift (n : ℕ) (h alpha : ℝ) (m : ℤ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op K w))
    (source target : E 2) :
    gridFactorResidual H alpha (modeLiftCLM n h m source) (modeLiftCLM n h m target) =
      modeLiftCLM n h m (factorResidual K alpha source target) := by
  rw [gridFactorResidual, den_intertwines (modeLiftCLM n h m) H K hJK alpha target,
    num_intertwines (modeLiftCLM n h m) H K hJK alpha source, ← map_sub]
  rfl

/-- Exact linear decomposition of the measured denominator residual. -/
theorem gridFactorResidual_superposition (n : ℕ) (h alpha : ℝ) (S : Finset ℤ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : ℤ → Mat 2)
    (hJK : ∀ m ∈ S, ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op (K m) w))
    (source target : ℤ → E 2) :
    gridFactorResidual H alpha (superpositionLift n h S source) (superpositionLift n h S target) =
      superpositionLift n h S (fun m => factorResidual (K m) alpha (source m) (target m)) := by
  unfold gridFactorResidual superpositionLift
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  exact gridFactorResidual_modeLift n h alpha m H (K m) (hJK m hm) (source m) (target m)

theorem gridFactorResidual_superposition_weighted_norm (M n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (H : Matrix (Grid n) (Grid n) ℂ) (K : ℤ → Mat 2)
    (source target : ℤ → E 2) (hh : 0 ≤ h)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hband : 2*M<n+1)
    (hS : ∀ m ∈ S, |(m:ℝ)| ≤ (M:ℝ))
    (hJK : ∀ m ∈ S, ∀ w, op H (modeLiftCLM n h m w) = modeLiftCLM n h m (op (K m) w)) :
    Real.sqrt h * ‖gridFactorResidual H alpha
      (superpositionLift n h S source) (superpositionLift n h S target)‖ =
      Real.sqrt (2*Real.pi) * coefficientNorm S
        (fun m => factorResidual (K m) alpha (source m) (target m)) := by
  rw [gridFactorResidual_superposition n h alpha S H K hJK source target]
  exact band_superposition_weighted_norm M n h hh hmesh S hband hS _

theorem hamiltonian_step_superposition (n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    step alpha (hamiltonian n h Z) (superpositionLift n h S a) =
      superpositionLift n h S (fun m => Chat (A (modeSymbol m h)) alpha (a m)) := by
  simp only [A, superpositionLift, map_sum,
    hamiltonian_step_modeLift n h alpha _ Z Z_isHermitian hmesh]

theorem potential_step_superposition (n : ℕ) (h alpha : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2) :
    step alpha (potential n X) (superpositionLift n h S a) =
      superpositionLift n h S (fun m => Chat B alpha (a m)) := by
  simp only [B, superpositionLift, map_sum,
    potential_step_modeLift n h alpha _ X X_isHermitian]

@[simp] theorem gridFactorResidual_step_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (alpha : ℝ) (hH : H.IsHermitian) (v : Vec ι) :
    gridFactorResidual H alpha v (step alpha H v) = 0 := by
  unfold gridFactorResidual
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, den_step alpha H hH, sub_self]

theorem frequency_final_stage_residual_bound (M : ℕ) (m : ℤ) (h k t : ℝ)
    (hM : 1 ≤ M) (hm : |(m:ℝ)| ≤ (M:ℝ)) (hh : 0<h)
    (hMh : (M:ℝ)*h ≤ 1) (hk : 0≤k) (hstep : 2*k*((M:ℝ)^2+2)≤1)
    (a : E 2) :
    ‖factorResidual (A (modeSymbol m h)) (k/4)
      (Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) (modeOrbit m t a)))
      (modeOrbit m (t+k) a)‖ ≤ (9/8)*k*(Ct M*k^2+Cs M*h^2)*‖a‖ := by
  have hb := frequency_stageResidualBudget_bound 1 M m h k
    hM hm hh hMh hk hstep (modeOrbit m t a)
  simp only [stageResidualBudget,
    factorResidual_cayley_zero (A (modeSymbol m h)) (k/4) (A_isHermitian _),
    factorResidual_cayley_zero B (k/2) B_isHermitian, weightedNorm_zero, zero_add,
    weightedNorm, Real.sqrt_one, one_mul, norm_zero, modeOrbit_norm] at hb
  rw [← modeOrbit_exact_step m a t k]
  simpa only [modeGenerator] using hb

/-- A derived bound on Exp007's actual full-grid three-stage residual budget.
No triangle sum over Fourier coefficients replaces the coefficient ℓ² norm. -/
theorem actual_superposition_stage_budget (M n : ℕ) (h k t : ℝ)
    (S : Finset ℤ) (a : ℤ → E 2)
    (hM : 1≤M) (hband : 2*M<n+1) (hS : ∀ m ∈ S, |(m:ℝ)|≤(M:ℝ))
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (hh : 0<h)
    (hMh : (M:ℝ)*h≤1) (hk : 0≤k) (hstep : 2*k*((M:ℝ)^2+2)≤1) :
    gridStageBudget n h k
      (superpositionLift n h S (fun m => modeOrbit m t (a m)))
      (step (k/4) (hamiltonian n h Z)
        (superpositionLift n h S (fun m => modeOrbit m t (a m))))
      (step (k/2) (potential n X) (step (k/4) (hamiltonian n h Z)
        (superpositionLift n h S (fun m => modeOrbit m t (a m)))))
      (superpositionLift n h S (fun m => modeOrbit m (t+k) (a m))) ≤
      Real.sqrt (2*Real.pi)*(9/8)*k*(Ct M*k^2+Cs M*h^2)*coefficientNorm S a := by
  let b := fun m => modeOrbit m t (a m)
  let q := fun m => Chat B (k/2) (Chat (A (modeSymbol m h)) (k/4) (b m))
  let target := fun m => modeOrbit m (t+k) (a m)
  let r := fun m => factorResidual (A (modeSymbol m h)) (k/4) (q m) (target m)
  have hct := Ct_nonneg M
  have hcs := Cs_nonneg M
  have hc : coefficientNorm S r ≤
      ((9/8)*k*(Ct M*k^2+Cs M*h^2))*coefficientNorm S a := by
    apply coefficientNorm_bound S a r _ (by positivity)
    intro m hm
    exact frequency_final_stage_residual_bound M m h k t hM (hS m hm) hh hMh hk hstep (a m)
  have hH := hamiltonian_isHermitian n h Z Z_isHermitian
  have hP := potential_isHermitian n X X_isHermitian
  change gridStageBudget n h k (superpositionLift n h S b)
    (step (k/4) (hamiltonian n h Z) (superpositionLift n h S b))
    (step (k/2) (potential n X) (step (k/4) (hamiltonian n h Z)
      (superpositionLift n h S b))) (superpositionLift n h S target) ≤ _
  simp only [gridStageBudget,
    gridFactorResidual_step_zero (hamiltonian n h Z) (k/4) hH,
    gridFactorResidual_step_zero (potential n X) (k/2) hP,
    norm_zero, mul_zero, zero_add]
  rw [hamiltonian_step_superposition n h (k/4) S b hmesh,
    potential_step_superposition n h (k/2) S]
  change Real.sqrt h*‖gridFactorResidual (hamiltonian n h Z) (k/4)
    (superpositionLift n h S q) (superpositionLift n h S target)‖ ≤ _
  rw [gridFactorResidual_superposition_weighted_norm M n h (k/4) S
    (hamiltonian n h Z) (fun m => A (modeSymbol m h)) q target hh.le hmesh hband hS
    (fun m _ w => hamiltonian_modeLift n h m Z hmesh w)]
  change Real.sqrt (2*Real.pi)*coefficientNorm S r ≤ _
  calc
    _ ≤ Real.sqrt (2*Real.pi)*(((9/8)*k*(Ct M*k^2+Cs M*h^2))*coefficientNorm S a) :=
      mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
    _ = _ := by ring

#print axioms gridFactorResidual_superposition
#print axioms gridFactorResidual_superposition_weighted_norm
#print axioms frequency_final_stage_residual_bound
#print axioms actual_superposition_stage_budget
end NDEAEvolve.Exp008
