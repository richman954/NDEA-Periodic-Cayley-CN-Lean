import Mathlib

noncomputable section

namespace NDEAMathlibGate
namespace ContinuousPDEGateV1

/-!
Scoped 1D heat-equation gate theorem.

This probe uses direct simp-style derivative proofs.
-/

def u (t x : ℝ) : ℝ :=
  x * x + 2 * t

def vBad (t x : ℝ) : ℝ :=
  x * x + t

def Dt (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun τ : ℝ => f τ x) t

def Dxx (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun y : ℝ => deriv (fun z : ℝ => f t z) y) x

def HeatResidual (f : ℝ → ℝ → ℝ) (t x : ℝ) : Prop :=
  Dt f t x = Dxx f t x

theorem u_dt (t x : ℝ) :
    Dt u t x = 2 := by
  unfold Dt u
  simp

theorem u_dx (t x : ℝ) :
    deriv (fun z : ℝ => u t z) x = 2 * x := by
  unfold u
  simp
  ring

theorem u_dxx (t x : ℝ) :
    Dxx u t x = 2 := by
  unfold Dxx
  have hfun : (fun y : ℝ => deriv (fun z : ℝ => u t z) y) = (fun y : ℝ => 2 * y) := by
    funext y
    exact u_dx t y
  rw [hfun]
  simp

theorem u_solves_heat_pointwise (t x : ℝ) :
    HeatResidual u t x := by
  unfold HeatResidual
  rw [u_dt, u_dxx]

theorem vBad_dt (t x : ℝ) :
    Dt vBad t x = 1 := by
  unfold Dt vBad
  simp

theorem vBad_dx (t x : ℝ) :
    deriv (fun z : ℝ => vBad t z) x = 2 * x := by
  unfold vBad
  simp
  ring

theorem vBad_dxx (t x : ℝ) :
    Dxx vBad t x = 2 := by
  unfold Dxx
  have hfun : (fun y : ℝ => deriv (fun z : ℝ => vBad t z) y) = (fun y : ℝ => 2 * y) := by
    funext y
    exact vBad_dx t y
  rw [hfun]
  simp

theorem vBad_not_heat_pointwise (t x : ℝ) :
    ¬ HeatResidual vBad t x := by
  intro h
  unfold HeatResidual at h
  rw [vBad_dt, vBad_dxx] at h
  norm_num at h

def continuousPDEGateStatusV1 : String :=
  "scoped_polynomial_heat_equation_gate_validated"

def broadContinuousPDEClaimStatusV1 : String :=
  "not_claimed"

theorem true_gate_status :
    continuousPDEGateStatusV1 = "scoped_polynomial_heat_equation_gate_validated" := by
  rfl

theorem true_broad_continuous_pde_not_claimed :
    broadContinuousPDEClaimStatusV1 = "not_claimed" := by
  rfl

#check u_solves_heat_pointwise
#check vBad_not_heat_pointwise

end ContinuousPDEGateV1
end NDEAMathlibGate
