import Mathlib
import NDEAMathlibGate.ContinuousPDEGateV1

noncomputable section

namespace NDEAMathlibGate
namespace ContinuousPDEGateV2_HeatLinearity

/-!
Continuous PDE Gate v2: structural heat-residual linearity.

This module proves a scoped structural theorem:

If f and g satisfy the pointwise HeatResidual at (t,x), and if Dt and Dxx
distribute over the linear combination a*f + b*g at (t,x), then the same
linear combination also satisfies HeatResidual at (t,x).

Scope:
  structural pointwise heat-residual linearity only;
  no broad continuous PDE formalization;
  no PDE existence/uniqueness theorem;
  no PML/operator theorem;
  no general gauge theorem.
-/

abbrev Dt : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
  NDEAMathlibGate.ContinuousPDEGateV1.Dt

abbrev Dxx : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ :=
  NDEAMathlibGate.ContinuousPDEGateV1.Dxx

abbrev HeatResidual : (ℝ → ℝ → ℝ) → ℝ → ℝ → Prop :=
  NDEAMathlibGate.ContinuousPDEGateV1.HeatResidual

/-- Pointwise real linear combination of two real-valued space-time functions. -/
def linComb (a b : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => a * f t x + b * g t x

/--
Structural heat-residual linearity.

This is intentionally conditional on the pointwise distribution laws for Dt and Dxx.
The analytic differentiability theorem proving those distribution laws is a later branch.
-/
theorem heatResidual_linear_combination_at
    (a b : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ)
    (hf : HeatResidual f t x)
    (hg : HeatResidual g t x)
    (hDt :
      Dt (linComb a b f g) t x =
        a * Dt f t x + b * Dt g t x)
    (hDxx :
      Dxx (linComb a b f g) t x =
        a * Dxx f t x + b * Dxx g t x) :
    HeatResidual (linComb a b f g) t x := by
  change Dt (linComb a b f g) t x = Dxx (linComb a b f g) t x
  change Dt f t x = Dxx f t x at hf
  change Dt g t x = Dxx g t x at hg
  rw [hDt, hDxx, hf, hg]

/--
Residual closure for the specific V1 heat-gate solution under explicit operator
linearity assumptions. This does not prove analytic derivative-linearity; it shows
the structural theorem applies to the previously verified solution.
-/
theorem heatResidual_linear_combination_of_V1_u_at
    (a b t x : ℝ)
    (hDt :
      Dt (linComb a b
        NDEAMathlibGate.ContinuousPDEGateV1.u
        NDEAMathlibGate.ContinuousPDEGateV1.u) t x =
        a * Dt NDEAMathlibGate.ContinuousPDEGateV1.u t x +
        b * Dt NDEAMathlibGate.ContinuousPDEGateV1.u t x)
    (hDxx :
      Dxx (linComb a b
        NDEAMathlibGate.ContinuousPDEGateV1.u
        NDEAMathlibGate.ContinuousPDEGateV1.u) t x =
        a * Dxx NDEAMathlibGate.ContinuousPDEGateV1.u t x +
        b * Dxx NDEAMathlibGate.ContinuousPDEGateV1.u t x) :
    HeatResidual
      (linComb a b
        NDEAMathlibGate.ContinuousPDEGateV1.u
        NDEAMathlibGate.ContinuousPDEGateV1.u) t x := by
  exact heatResidual_linear_combination_at
    a b
    NDEAMathlibGate.ContinuousPDEGateV1.u
    NDEAMathlibGate.ContinuousPDEGateV1.u
    t x
    (NDEAMathlibGate.ContinuousPDEGateV1.u_solves_heat_pointwise t x)
    (NDEAMathlibGate.ContinuousPDEGateV1.u_solves_heat_pointwise t x)
    hDt hDxx

def continuousPDEGateStatusV2 : String :=
  "structural_heat_residual_linearity_validated"

def analyticDerivativeLinearityStatusV2 : String :=
  "not_claimed"

def broadContinuousPDEClaimStatusV2 : String :=
  "not_claimed"

def pmlOperatorClaimStatusV2 : String :=
  "not_claimed"

def generalGaugeClaimStatusV2 : String :=
  "not_claimed"

theorem true_gate_status :
    continuousPDEGateStatusV2 = "structural_heat_residual_linearity_validated" := by
  rfl

theorem true_analytic_derivative_linearity_not_claimed :
    analyticDerivativeLinearityStatusV2 = "not_claimed" := by
  rfl

theorem true_broad_continuous_pde_not_claimed :
    broadContinuousPDEClaimStatusV2 = "not_claimed" := by
  rfl

theorem true_pml_operator_not_claimed :
    pmlOperatorClaimStatusV2 = "not_claimed" := by
  rfl

theorem true_general_gauge_not_claimed :
    generalGaugeClaimStatusV2 = "not_claimed" := by
  rfl

#check heatResidual_linear_combination_at
#check heatResidual_linear_combination_of_V1_u_at
#check true_gate_status
#check true_broad_continuous_pde_not_claimed

end ContinuousPDEGateV2_HeatLinearity
end NDEAMathlibGate
