import ForcedStability
import ResidualField

/-! A posteriori error estimates against a classical periodic solution.
Every residual here is the actual derivative expression from ResidualField. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem residual_error_to_classical (w u : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField L w)
    (hu : Exp013.IsClassicalPeriodicSolution L V f u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hdefect : Continuous (fun p : ℝ × ℝ => pdeResidual V w p.1 p.2 - f p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (fun x => w t x - u t x) b L ≤
      spatialL2 (fun x => w s x - u s x) b L +
        ∫ r in s..t, spatialL2 (fun x => pdeResidual V w r x - f r x) b L :=
  classical_forcing_stability w u (regular_classical_residual V w hw) hu
    hV hL hdefect b s t hst

theorem residual_error_homogeneous (w u : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField L w)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hres : Continuous (fun p : ℝ × ℝ => pdeResidual V w p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (fun x => w t x - u t x) b L ≤
      spatialL2 (fun x => w s x - u s x) b L +
        ∫ r in s..t, spatialL2 (pdeResidual V w r) b L := by
  simpa only [Pi.zero_apply, sub_zero] using
    residual_error_to_classical w u hw hu hV hL (by simpa using hres) b s t hst

theorem residual_error_continuous_potential (w u : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField L w)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hVc : Continuous (fun p : ℝ × ℝ => V p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (fun x => w t x - u t x) b L ≤
      spatialL2 (fun x => w s x - u s x) b L +
        ∫ r in s..t, spatialL2 (pdeResidual V w r) b L :=
  residual_error_homogeneous w u hw hu hV hL (pdeResidual_continuous V w hw hVc) b s t hst

theorem residual_error_exact_initialization (w u : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField L w)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hres : Continuous (fun p : ℝ × ℝ => pdeResidual V w p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) (hinit : ∀ x, w s x = u s x) :
    spatialL2 (fun x => w t x - u t x) b L ≤
      ∫ r in s..t, spatialL2 (pdeResidual V w r) b L := by
  have h := residual_error_homogeneous w u hw hu hV hL hres b s t hst
  have he : (fun x => w s x - u s x) = (0 : ℝ → H) :=
    funext fun x => sub_eq_zero.mpr (hinit x)
  rw [he, spatialL2_zero, zero_add] at h
  exact h

theorem residual_error_uniform_budget (w u : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField L w)
    (hu : Exp013.IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hres : Continuous (fun p : ℝ × ℝ => pdeResidual V w p.1 p.2))
    (b s t δ : ℝ) (hst : s ≤ t)
    (hbudget : ∀ r ∈ Set.Icc s t, spatialL2 (pdeResidual V w r) b L ≤ δ) :
    spatialL2 (fun x => w t x - u t x) b L ≤
      spatialL2 (fun x => w s x - u s x) b L + (t-s)*δ := by
  have h := residual_error_homogeneous w u hw hu hV hL hres b s t hst
  have hc := spatialL2_time_continuous (pdeResidual V w) hres b L
  have hi := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable s t)
    (continuous_const.intervalIntegrable s t : IntervalIntegrable (fun _ : ℝ => δ) volume s t)
    hbudget
  have hi' : (∫ r in s..t, spatialL2 (pdeResidual V w r) b L) ≤ (t-s)*δ := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  linarith

end NDEAEvolve.Exp015
