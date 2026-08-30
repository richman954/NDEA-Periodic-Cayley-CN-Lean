import Mathlib
import NDEAMathlibGate.ContinuousPDEGateV2_HeatLinearity

noncomputable section

namespace NDEAMathlibGate
namespace ContinuousPDEGateV3R_AnalyticDerivativeLinearity

/-!
Continuous PDE Gate v3R: analytic derivative-linearity repair.

This repairs the V3 function-extensionality mismatch. Mathlib's
HasDerivAt.add gives derivatives of function-addition expressions such as

  (fun y => a * f y x) + (fun y => b * g y x)

whereas the PDE definitions use lambda-sum expressions such as

  fun y => a * f y x + b * g y x.

The repair explicitly rewrites between those forms using funext.

Scope:
  pointwise analytic derivative-linearity from HasDerivAt hypotheses;
  no PDE existence/uniqueness theorem;
  no broad continuous PDE formalization;
  no PML/operator theorem;
  no general gauge theorem.
-/

abbrev Dt : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
  NDEAMathlibGate.ContinuousPDEGateV1.Dt

abbrev Dxx : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
  NDEAMathlibGate.ContinuousPDEGateV1.Dxx

abbrev HeatResidual : (ℝ → ℝ → ℝ) → ℝ → ℝ → Prop :=
  NDEAMathlibGate.ContinuousPDEGateV1.HeatResidual

abbrev linComb : ℝ → ℝ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
  NDEAMathlibGate.ContinuousPDEGateV2_HeatLinearity.linComb

/-- First spatial derivative wrapper used to state second-derivative hypotheses. -/
def Dx (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun z : ℝ => f t z) x

/-- Explicit function-addition to lambda-sum bridge. -/
theorem fun_add_eq_lambda_add_time
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (x : ℝ) :
    ((fun τ : ℝ => a * f τ x) + (fun τ : ℝ => b * g τ x))
      =
    (fun τ : ℝ => a * f τ x + b * g τ x) := by
  funext τ
  rfl

/-- Explicit spatial function-addition to lambda-sum bridge. -/
theorem fun_add_eq_lambda_add_space
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t : ℝ) :
    ((fun z : ℝ => a * f t z) + (fun z : ℝ => b * g t z))
      =
    (fun z : ℝ => a * f t z + b * g t z) := by
  funext z
  rfl

/-- Explicit first-derivative function-addition to lambda-sum bridge. -/
theorem fun_add_eq_lambda_add_dx
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t : ℝ) :
    ((fun y : ℝ => a * Dx f t y) + (fun y : ℝ => b * Dx g t y))
      =
    (fun y : ℝ => a * Dx f t y + b * Dx g t y) := by
  funext y
  rfl

/--
Time-derivative linearity from Mathlib HasDerivAt hypotheses.
-/
theorem Dt_linear_of_hasDerivAt
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ)
    (hf : HasDerivAt (fun τ : ℝ => f τ x) (Dt f t x) t)
    (hg : HasDerivAt (fun τ : ℝ => g τ x) (Dt g t x) t) :
    Dt (linComb a b f g) t x =
      a * Dt f t x + b * Dt g t x := by
  have hsum :
      deriv (((fun τ : ℝ => a * f τ x) + (fun τ : ℝ => b * g τ x))) t =
        a * Dt f t x + b * Dt g t x :=
    ((hf.const_mul a).add (hg.const_mul b)).deriv
  change deriv (fun τ : ℝ => a * f τ x + b * g τ x) t =
    a * Dt f t x + b * Dt g t x
  rw [← fun_add_eq_lambda_add_time a b f g x]
  exact hsum

/--
First spatial derivative linearity from HasDerivAt hypotheses on spatial slices.
-/
theorem Dx_linear_of_hasDerivAt
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ)
    (hf : HasDerivAt (fun z : ℝ => f t z) (Dx f t x) x)
    (hg : HasDerivAt (fun z : ℝ => g t z) (Dx g t x) x) :
    Dx (linComb a b f g) t x =
      a * Dx f t x + b * Dx g t x := by
  have hsum :
      deriv (((fun z : ℝ => a * f t z) + (fun z : ℝ => b * g t z))) x =
        a * Dx f t x + b * Dx g t x :=
    ((hf.const_mul a).add (hg.const_mul b)).deriv
  change deriv (fun z : ℝ => a * f t z + b * g t z) x =
    a * Dx f t x + b * Dx g t x
  rw [← fun_add_eq_lambda_add_space a b f g t]
  exact hsum

/--
Second-spatial-derivative linearity from Mathlib HasDerivAt hypotheses.

The hypotheses say:
  * each spatial slice of f and g has first derivative at every y,
  * the first-derivative functions y ↦ Dx f t y and y ↦ Dx g t y
    have derivatives Dxx f t x and Dxx g t x at x.
-/
theorem Dxx_linear_of_hasDerivAt
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ)
    (hf_dx : ∀ y : ℝ, HasDerivAt (fun z : ℝ => f t z) (Dx f t y) y)
    (hg_dx : ∀ y : ℝ, HasDerivAt (fun z : ℝ => g t z) (Dx g t y) y)
    (hf_dxx : HasDerivAt (fun y : ℝ => Dx f t y) (Dxx f t x) x)
    (hg_dxx : HasDerivAt (fun y : ℝ => Dx g t y) (Dxx g t x) x) :
    Dxx (linComb a b f g) t x =
      a * Dxx f t x + b * Dxx g t x := by
  change
    deriv (fun y : ℝ =>
      deriv (fun z : ℝ => linComb a b f g t z) y) x =
      a * Dxx f t x + b * Dxx g t x
  have hinner :
      (fun y : ℝ =>
        deriv (fun z : ℝ => linComb a b f g t z) y)
      =
      (fun y : ℝ =>
        a * Dx f t y + b * Dx g t y) := by
    funext y
    exact Dx_linear_of_hasDerivAt a b f g t y (hf_dx y) (hg_dx y)
  rw [hinner]
  have hsum :
      deriv (((fun y : ℝ => a * Dx f t y) + (fun y : ℝ => b * Dx g t y))) x =
        a * Dxx f t x + b * Dxx g t x :=
    ((hf_dxx.const_mul a).add (hg_dxx.const_mul b)).deriv
  rw [← fun_add_eq_lambda_add_dx a b f g t]
  exact hsum

/--
Analytic lift of the v2 structural heat-linearity theorem.

Instead of assuming Dt and Dxx distribution directly, this theorem derives them
from HasDerivAt hypotheses and then applies the v2 structural theorem.
-/
theorem heatResidual_linear_combination_of_hasDerivAt
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ)
    (hf_heat : HeatResidual f t x)
    (hg_heat : HeatResidual g t x)
    (hf_dt : HasDerivAt (fun τ : ℝ => f τ x) (Dt f t x) t)
    (hg_dt : HasDerivAt (fun τ : ℝ => g τ x) (Dt g t x) t)
    (hf_dx : ∀ y : ℝ, HasDerivAt (fun z : ℝ => f t z) (Dx f t y) y)
    (hg_dx : ∀ y : ℝ, HasDerivAt (fun z : ℝ => g t z) (Dx g t y) y)
    (hf_dxx : HasDerivAt (fun y : ℝ => Dx f t y) (Dxx f t x) x)
    (hg_dxx : HasDerivAt (fun y : ℝ => Dx g t y) (Dxx g t x) x) :
    HeatResidual (linComb a b f g) t x := by
  exact
    NDEAMathlibGate.ContinuousPDEGateV2_HeatLinearity.heatResidual_linear_combination_at
      a b f g t x
      hf_heat
      hg_heat
      (Dt_linear_of_hasDerivAt a b f g t x hf_dt hg_dt)
      (Dxx_linear_of_hasDerivAt a b f g t x hf_dx hg_dx hf_dxx hg_dxx)

def continuousPDEGateStatusV3R : String :=
  "analytic_derivative_linearity_lift_validated"

def analyticDerivativeLinearityStatusV3R : String :=
  "hasDerivAt_pointwise_lift_validated"

def broadContinuousPDEClaimStatusV3R : String :=
  "not_claimed"

def pmlOperatorClaimStatusV3R : String :=
  "not_claimed"

def generalGaugeClaimStatusV3R : String :=
  "not_claimed"

theorem true_gate_status :
    continuousPDEGateStatusV3R = "analytic_derivative_linearity_lift_validated" := by
  rfl

theorem true_analytic_derivative_linearity_status :
    analyticDerivativeLinearityStatusV3R = "hasDerivAt_pointwise_lift_validated" := by
  rfl

theorem true_broad_continuous_pde_not_claimed :
    broadContinuousPDEClaimStatusV3R = "not_claimed" := by
  rfl

theorem true_pml_operator_not_claimed :
    pmlOperatorClaimStatusV3R = "not_claimed" := by
  rfl

theorem true_general_gauge_not_claimed :
    generalGaugeClaimStatusV3R = "not_claimed" := by
  rfl

#check Dt_linear_of_hasDerivAt
#check Dx_linear_of_hasDerivAt
#check Dxx_linear_of_hasDerivAt
#check heatResidual_linear_combination_of_hasDerivAt
#check true_gate_status
#check true_broad_continuous_pde_not_claimed

end ContinuousPDEGateV3R_AnalyticDerivativeLinearity
end NDEAMathlibGate
