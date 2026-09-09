import RegularSynthesis
import SpatialL2Bridge
import QuadraticNorm
import FourierNorm
import FourierSynthesisRegular

/-! A computed spatial L2 budget for the actual quadratic PDE residual.
The endpoint defect and the three spatial discrepancy terms remain explicit.
The full odd-grid Fourier reconstruction supplies the norm identity directly. -/
noncomputable section
open Set
namespace NDEAEvolve.Exp016
open Exp015

section Generic
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem qpde_linear_combination_bound (u v w : ℝ → H) (a c : ℂ)
    (b L : ℝ) (hL : 0 ≤ L) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) :
    spatialL2 (fun x => u x + a • v x - c • w x) b L ≤
      spatialL2 u b L + ‖a‖ * spatialL2 v b L + ‖c‖ * spatialL2 w b L := by
  have h₁ := spatialL2_add_le u (fun x => a • v x) b L hL hu
    (continuous_const.smul hv)
  have h₂ := spatialL2_add_le (fun x => u x + a • v x)
    (fun x => -(c • w x)) b L hL (hu.add (continuous_const.smul hv))
    (continuous_const.smul hw).neg
  rw [spatialL2_neg, spatialL2_smul] at h₂
  rw [spatialL2_smul] at h₁
  simpa only [sub_eq_add_neg] using le_trans h₂ (add_le_add h₁ le_rfl)

namespace RegularSynthesis
variable {L : ℝ} (S : RegularSynthesis E H L)

theorem spatialDefect_apply_continuous (G : E →L[ℂ] E)
    (V : ℝ → H →L[ℂ] H) (hV : Continuous V) (z : E) :
    Continuous (fun x => S.spatialDefect G V x z) := by
  change Continuous (fun x => S.eval x (G z) + S.dxx x z - V x (S.eval x z))
  exact ((S.continuous_eval.clm_apply continuous_const).add
    (S.continuous_dxx.clm_apply continuous_const)).sub
    (hV.clm_apply (S.continuous_eval.clm_apply continuous_const))

theorem quadratic_spatialDefect_spatialL2_le (G : E →L[ℂ] E)
    (V : ℝ → H →L[ℂ] H) (hV : Continuous V) (m v : E)
    (b t₀ k t : ℝ) (hL : 0 ≤ L) (ht : t ∈ Icc t₀ (t₀ + k)) :
    spatialL2 (fun x => S.spatialDefect G V x (quadraticTime G m v t₀ k t)) b L ≤
      spatialL2 (fun x => S.spatialDefect G V x m) b L +
        (k / 2) * spatialL2 (fun x => S.spatialDefect G V x v) b L +
        (k ^ 2 / 8) * spatialL2 (fun x => S.spatialDefect G V x (G v)) b L := by
  have h := qpde_linear_combination_bound
    (fun x => S.spatialDefect G V x m) (fun x => S.spatialDefect G V x v)
    (fun x => S.spatialDefect G V x (G v))
    (quadraticOffset t₀ k t : ℂ) (quadraticCorrection t₀ k t) b L hL
    (S.spatialDefect_apply_continuous G V hV m)
    (S.spatialDefect_apply_continuous G V hV v)
    (S.spatialDefect_apply_continuous G V hV (G v))
  have he : (fun x => S.spatialDefect G V x (quadraticTime G m v t₀ k t)) =
      (fun x => S.spatialDefect G V x m +
        (quadraticOffset t₀ k t : ℂ) • S.spatialDefect G V x v -
        quadraticCorrection t₀ k t • S.spatialDefect G V x (G v)) := by
    funext x
    simp only [quadraticTime, map_add, map_sub, map_smul]
  rw [he]
  apply le_trans h
  apply add_le_add
  · apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (spatialL2_nonneg _ b L)
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      quadraticOffset_abs_le t₀ k t ht
  · exact mul_le_mul_of_nonneg_right (quadraticCorrection_norm_le t₀ k t ht)
      (spatialL2_nonneg _ b L)

theorem quadratic_field_residual_spatialL2_le (G : E →L[ℂ] E)
    (V : ℝ → H →L[ℂ] H) (hV : Continuous V) (m v : E)
    (b ρ t₀ k t : ℝ) (hL : 0 ≤ L)
    (hS : ∀ z : E, spatialL2 (fun x => S.eval x z) b L = ρ * ‖z‖)
    (ht : t ∈ Icc t₀ (t₀ + k)) :
    spatialL2 (Exp015.pdeResidual (fun _ => V)
      (S.field (quadraticTime G m v t₀ k)) t) b L ≤
      ρ * (‖Complex.I • v - G m‖ + (k ^ 2 / 8) * ‖G (G v)‖) +
        spatialL2 (fun x => S.spatialDefect G V x m) b L +
        (k / 2) * spatialL2 (fun x => S.spatialDefect G V x v) b L +
        (k ^ 2 / 8) * spatialL2 (fun x => S.spatialDefect G V x (G v)) b L := by
  let u : ℝ → H := fun x => S.eval x (Complex.I • v - G m)
  let w : ℝ → H := fun x => S.eval x (G (G v))
  let d : ℝ → H := fun x => S.spatialDefect G V x (quadraticTime G m v t₀ k t)
  have hu : Continuous u := S.continuous_eval.clm_apply continuous_const
  have hw : Continuous w := S.continuous_eval.clm_apply continuous_const
  have hd : Continuous d := S.spatialDefect_apply_continuous G V hV _
  have h₁ := spatialL2_add_le u (fun x => quadraticCorrection t₀ k t • w x)
    b L hL hu (continuous_const.smul hw)
  rw [spatialL2_smul] at h₁
  have h₂ := spatialL2_add_le
    (fun x => u x + quadraticCorrection t₀ k t • w x) d b L hL
    (hu.add (continuous_const.smul hw)) hd
  have hq := S.quadratic_spatialDefect_spatialL2_le G V hV m v b t₀ k t hL ht
  have hc := mul_le_mul_of_nonneg_right (quadraticCorrection_norm_le t₀ k t ht)
    (spatialL2_nonneg w b L)
  have he : Exp015.pdeResidual (fun _ => V)
      (S.field (quadraticTime G m v t₀ k)) t =
      (fun x => u x + quadraticCorrection t₀ k t • w x + d x) := by
    funext x
    exact S.quadratic_field_residual G V m v t₀ k t x
  rw [he]
  calc
    spatialL2 (fun x => u x + quadraticCorrection t₀ k t • w x + d x) b L ≤
        spatialL2 u b L + (k ^ 2 / 8) * spatialL2 w b L + spatialL2 d b L :=
      le_trans h₂ (add_le_add (le_trans h₁ (add_le_add le_rfl hc)) le_rfl)
    _ ≤ spatialL2 u b L + (k ^ 2 / 8) * spatialL2 w b L +
        (spatialL2 (fun x => S.spatialDefect G V x m) b L +
          (k / 2) * spatialL2 (fun x => S.spatialDefect G V x v) b L +
          (k ^ 2 / 8) * spatialL2 (fun x => S.spatialDefect G V x (G v)) b L) :=
      add_le_add le_rfl hq
    _ = _ := by
      dsimp only [u, w]
      rw [hS, hS]
      ring

end RegularSynthesis
end Generic

open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid

theorem fourier_quadratic_residual_spatialL2_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (G : Vec (Grid (2 * M)) →L[ℂ] Vec (Grid (2 * M)))
    (V : ℝ → E 2 →L[ℂ] E 2) (hV : Continuous V) (m v : Vec (Grid (2 * M)))
    (b t₀ k t : ℝ) (ht : t ∈ Icc t₀ (t₀ + k)) :
    spatialL2 (Exp015.pdeResidual (fun _ => V)
      (fun s => fourierReconstruction M h (quadraticTime G m v t₀ k s)) t)
        b (2 * Real.pi) ≤
      Real.sqrt h * (‖Complex.I • v - G m‖ + (k ^ 2 / 8) * ‖G (G v)‖) +
        spatialL2 (fun x => (fourierRegularSynthesis M h).spatialDefect G V x m)
          b (2 * Real.pi) +
        (k / 2) * spatialL2 (fun x => (fourierRegularSynthesis M h).spatialDefect G V x v)
          b (2 * Real.pi) +
        (k ^ 2 / 8) * spatialL2
          (fun x => (fourierRegularSynthesis M h).spatialDefect G V x (G v)) b (2 * Real.pi) := by
  rw [← fourierRegularSynthesis_field]
  apply (fourierRegularSynthesis M h).quadratic_field_residual_spatialL2_le
    G V hV m v b (Real.sqrt h) t₀ k t (by positivity) _ ht
  intro z
  simpa only [fourierRegularSynthesis_eval] using
    fourierReconstruction_spatialL2 M h hmesh z b

#print axioms RegularSynthesis.spatialDefect_apply_continuous
#print axioms RegularSynthesis.quadratic_spatialDefect_spatialL2_le
#print axioms RegularSynthesis.quadratic_field_residual_spatialL2_le
#print axioms fourier_quadratic_residual_spatialL2_le
end NDEAEvolve.Exp016
