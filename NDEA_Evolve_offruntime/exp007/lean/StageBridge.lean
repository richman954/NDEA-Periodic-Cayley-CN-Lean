import FullClosure

/-! The full-grid denominator residual budget equals the existing Exp005
budget on the invariant spinor space, including the physical norm factor. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp007
open SpinorGrid

def gridFactorResidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (a : ℝ) (source target : Vec ι) : Vec ι :=
  op (den a H) target - op (num a H) source

def gridStageBudget (n : ℕ) (h k : ℝ)
    (source first second target : Vec (Grid n)) : ℝ :=
  Real.sqrt h * ‖gridFactorResidual (hamiltonian n h Z) (k/4) source first‖ +
  Real.sqrt h * ‖gridFactorResidual (potential n X) (k/2) first second‖ +
  Real.sqrt h * ‖gridFactorResidual (hamiltonian n h Z) (k/4) second target‖

theorem gridFactorResidual_lift (n : ℕ) (h a : ℝ)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (liftCLM n h w) = liftCLM n h (op K w)) (source target : E 2) :
    gridFactorResidual H a (liftCLM n h source) (liftCLM n h target) =
      liftCLM n h (factorResidual K a source target) := by
  rw [gridFactorResidual, den_intertwines (liftCLM n h) H K hJK a target,
    num_intertwines (liftCLM n h) H K hJK a source, ← map_sub]
  rfl

theorem gridFactorResidual_weighted_lift (n : ℕ) (h a : ℝ)
    (hh : 0 ≤ h) (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (H : Matrix (Grid n) (Grid n) ℂ) (K : Mat 2)
    (hJK : ∀ w, op H (liftCLM n h w) = liftCLM n h (op K w)) (source target : E 2) :
    Real.sqrt h * ‖gridFactorResidual H a (liftCLM n h source) (liftCLM n h target)‖ =
      weightedNorm (2*Real.pi) (factorResidual K a source target) := by
  rw [gridFactorResidual_lift n h a H K hJK source target]
  exact lift_weighted_norm n h hh hmesh _

/-- Exact equality with Exp005's actual three-stage residual budget. -/
theorem gridStageBudget_eq_exp005 (n : ℕ) (h k : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi) (source first second target : E 2) :
    gridStageBudget n h k (liftCLM n h source) (liftCLM n h first)
      (liftCLM n h second) (liftCLM n h target) =
    stageResidualBudget (2*Real.pi) k (A (Exp006.spatialSymbol h)) B
      source first second target := by
  unfold gridStageBudget stageResidualBudget
  rw [gridFactorResidual_weighted_lift n h (k/4) hh hmesh _ _
        (hamiltonian_intertwines n h Z hmesh),
      gridFactorResidual_weighted_lift n h (k/2) hh hmesh _ _
        (potential_intertwines n h X),
      gridFactorResidual_weighted_lift n h (k/4) hh hmesh _ _
        (hamiltonian_intertwines n h Z hmesh)]
  rfl

theorem actual_noncommuting_stage_budget (n : ℕ) (h k t : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 1/6) (v0 : E 2) :
    gridStageBudget n h k (liftCLM n h (v v0 t))
      (step (k/4) (hamiltonian n h Z) (liftCLM n h (v v0 t)))
      (step (k/2) (potential n X)
        (step (k/4) (hamiltonian n h Z) (liftCLM n h (v v0 t))))
      (liftCLM n h (v v0 (t+k))) ≤
    Real.sqrt (2*Real.pi)*k*(29250*k^2+13*h^2/96)*‖v0‖ := by
  rw [hamiltonian_step_lift n h (k/4) Z Z_isHermitian hmesh,
    potential_step_lift n h (k/2) X X_isHermitian,
    gridStageBudget_eq_exp005 n h k hh.le hmesh,
    ← v_exact_step v0 t k]
  have hb := reduced_stageResidualBudget_bound h k hh hhsmall hk hksmall (v v0 t)
  rwa [v_norm] at hb

/-- The lifted reference is literally the sampled continuum PDE solution. -/
theorem lift_reference_is_sampled_U (n : ℕ) (h t : ℝ) (v0 : E 2)
    (j : Fin (n+1)) (a : Fin 2) :
    liftCLM n h (v v0 t) (j,a) = U v0 t ((j.val : ℝ)*h) a := rfl

theorem actual_grid_noncommutes (n : ℕ) (h : ℝ) :
    ¬ Commute (hamiltonian n h Z) (potential n X) := by
  apply hamiltonian_noncommutes_potential n h Z X
  simpa [A, B] using A_noncommutes_B 0

#print axioms gridStageBudget_eq_exp005
#print axioms actual_noncommuting_stage_budget
#print axioms lift_reference_is_sampled_U
#print axioms actual_grid_noncommutes
end NDEAEvolve.Exp007
