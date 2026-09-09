import SpatialL2
import ScalarSqrtEstimate
import GenericUniqueness

/-! Quantitative L2 stability from the actual classical PDE and its forcing.
The forcing difference is jointly continuous; no division by the error norm
is used, so the estimate includes exactly matching initial data. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f g : ℝ → ℝ → H}

theorem classical_l2_le_initial_add_forcing (u : ℝ → ℝ → H)
    (hu : Exp013.IsClassicalPeriodicSolution L V f u)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (u t) b L ≤ spatialL2 (u s) b L +
      ∫ r in s..t, spatialL2 (f r) b L := by
  have hE : ∀ r, 0 ≤ Exp013.energy u b L r := by
    intro r
    rw [← spatialL2_sq_eq_energy u b L r hL.le]
    exact sq_nonneg _
  have hder := fun r => Exp013.energy_time_hasDerivAt_work u hu hV b r
  have hF := spatialL2_time_continuous f hf b L
  have hbound : ∀ r, (∫ x in b..b+L, Exp013.forcingWork f u r x) ≤
      2 * Real.sqrt (Exp013.energy u b L r) * spatialL2 (f r) b L := by
    intro r
    exact forcingWork_integral_le f u b L r hL.le
      (hf.comp (continuous_const.prodMk continuous_id))
      (hu.continuous_solution.comp (continuous_const.prodMk continuous_id))
  exact sqrt_energy_le_initial_add_integral (Exp013.energy u b L)
    (fun r => ∫ x in b..b+L, Exp013.forcingWork f u r x)
    (fun r => spatialL2 (f r) b L) hE hder hF
    (fun r => spatialL2_nonneg (f r) b L) hbound s t hst

theorem classical_forcing_stability (u v : ℝ → ℝ → H)
    (hu : Exp013.IsClassicalPeriodicSolution L V f u)
    (hv : Exp013.IsClassicalPeriodicSolution L V g v)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (hL : 0 < L)
    (hfg : Continuous (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2))
    (b s t : ℝ) (hst : s ≤ t) :
    spatialL2 (fun x => u t x - v t x) b L ≤
      spatialL2 (fun x => u s x - v s x) b L +
        ∫ r in s..t, spatialL2 (fun x => f r x - g r x) b L :=
  classical_l2_le_initial_add_forcing (fun r x => u r x - v r x)
    (Exp013.classical_sub u v hu hv) hV hL hfg b s t hst

theorem classical_same_forcing_l2_eq (u v : ℝ → ℝ → H)
    (hu : Exp013.IsClassicalPeriodicSolution L V f u)
    (hv : Exp013.IsClassicalPeriodicSolution L V f v)
    (hV : ∀ r x, IsSelfAdjoint (V r x)) (b s t : ℝ) :
    spatialL2 (fun x => u t x - v t x) b L =
      spatialL2 (fun x => u s x - v s x) b L := by
  exact congrArg Real.sqrt
    (Exp013.classical_difference_energy_conserved u v hu hv hV b t s)

end NDEAEvolve.Exp015
