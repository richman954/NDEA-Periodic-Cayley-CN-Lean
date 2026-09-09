import ResidualEstimate
import ClassicalExistence

/-! Residual estimates against the actual global solution constructed in Exp014.
This specializes the generic bound to regular static Fourier potentials. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NDEAEvolve.Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem variable_potential_residual_error (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (b₀ : Exp014.FourierState H) (w : ℝ → ℝ → H)
    (hw : IsRegularPeriodicField (2 * Real.pi) w)
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (fun x => w t x - Exp014.solution v b₀ t x) b (2 * Real.pi) ≤
      spatialL2 (fun x => w s x - Exp014.solution v b₀ s x) b (2 * Real.pi) +
        ∫ r in s..t, spatialL2 (pdeResidual (fun _ x => Exp014.operatorPotential v x) w r)
          b (2 * Real.pi) :=
  residual_error_continuous_potential w (Exp014.solution v b₀) hw
    (Exp014.solution_classical v hv b₀)
    (fun _ x => Exp014.operatorPotential_selfAdjoint v hHerm x)
    (by positivity : 0 < 2 * Real.pi)
    ((Exp014.operatorPotential_continuous v hv).comp continuous_snd) b s t hst

theorem variable_potential_error_from_fourier_data (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : ℤ → H) (ha : Summable (fun m => Exp014.weight m * ‖a m‖))
    (w : ℝ → ℝ → H) (hw : IsRegularPeriodicField (2 * Real.pi) w)
    (b t : ℝ) (ht : 0 ≤ t) :
    spatialL2 (fun x => w t x - Exp014.solution v (Exp014.ofCoefficients a ha) t x)
      b (2 * Real.pi) ≤
      spatialL2 (fun x => w 0 x - ∑' m, Exp014.character x m • a m) b (2 * Real.pi) +
        ∫ r in 0..t, spatialL2 (pdeResidual (fun _ x => Exp014.operatorPotential v x) w r)
          b (2 * Real.pi) := by
  have h := variable_potential_residual_error v hv hHerm (Exp014.ofCoefficients a ha)
    w hw b 0 t ht
  simpa only [Exp014.solution_zero, Exp014.synth_eq_tsum,
    Exp014.coefficient_ofCoefficients] using h

theorem variable_potential_error_exact_fourier_initialization (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : ℤ → H) (ha : Summable (fun m => Exp014.weight m * ‖a m‖))
    (w : ℝ → ℝ → H) (hw : IsRegularPeriodicField (2 * Real.pi) w)
    (hinit : ∀ x, w 0 x = ∑' m, Exp014.character x m • a m)
    (b t : ℝ) (ht : 0 ≤ t) :
    spatialL2 (fun x => w t x - Exp014.solution v (Exp014.ofCoefficients a ha) t x)
      b (2 * Real.pi) ≤
      ∫ r in 0..t, spatialL2 (pdeResidual (fun _ x => Exp014.operatorPotential v x) w r)
        b (2 * Real.pi) := by
  have h := variable_potential_error_from_fourier_data v hv hHerm a ha w hw b t ht
  have he : (fun x => w 0 x - ∑' m, Exp014.character x m • a m) = (0 : ℝ → H) :=
    funext fun x => sub_eq_zero.mpr (hinit x)
  rw [he, spatialL2_zero, zero_add] at h
  exact h

end NDEAEvolve.Exp015
