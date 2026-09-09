import GenericClassical
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Energy balance and homogeneous conservation in a complex Hilbert space.
The derivative majorant is obtained on local compact rectangles. The potential
may vary in time and position; only its pointwise self-adjointness is used. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval
namespace NDEAEvolve.Exp013

theorem compact_derivative_bound (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b t : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Ioo (t-1) (t+1), ∀ x ∈ uIcc a b, ‖g s x‖ ≤ C := by
  have hcompact : IsCompact (Icc (t-1) (t+1) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C,?_⟩
  intro s hs x hx
  exact hC (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩

theorem joint_interval_hasDerivAt (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hd : ∀ s x, HasDerivAt (fun t => f t x) (g s x) s) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f s x) (∫ x in a..b, g t x) t := by
  obtain ⟨C,hC⟩ := compact_derivative_bound g hg a b t
  have hf_slice (s : ℝ) : Continuous (f s) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hg_slice (s : ℝ) : Continuous (g s) :=
    hg.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := g) (a := a) (b := b)
    (s := Ioo (t-1) (t+1)) (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Ioo_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall fun s => (hf_slice s).aestronglyMeasurable
  · exact (hf_slice t).intervalIntegrable a b
  · exact (hg_slice t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x hx s hs => hC s hs x (uIoc_subset_uIcc hx)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ s _ => hd s x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energy (u : ℝ → ℝ → H) (b L t : ℝ) : ℝ :=
  ∫ x in b..b+L, ‖u t x‖^2

variable {L : ℝ} {V : ℝ → ℝ → H →L[ℂ] H} {f : ℝ → ℝ → H}

theorem energy_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fun x => ‖u t x‖^2) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (energyDensity u t) := (energyDensity_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem densityDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (densityDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (densityDerivative u t) := (densityDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem fluxDerivative_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    IntervalIntegrable (fluxDerivative u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fluxDerivative u t) := (fluxDerivative_continuous u hu).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem forcingWork_intervalIntegrable (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    IntervalIntegrable (forcingWork f u t) volume b (b+L) := by
  have hp : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hc : Continuous (forcingWork f u t) := (forcingWork_continuous u hu hV).comp hp
  exact hc.intervalIntegrable b (b+L)

theorem energy_time_hasDerivAt (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, densityDerivative u t x) t :=
  joint_interval_hasDerivAt (energyDensity u) (densityDerivative u)
    (energyDensity_continuous u hu) (densityDerivative_continuous u hu)
    (density_time_hasDerivAt u hu) b (b+L) t

theorem fluxDerivative_integral_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u) (b t : ℝ) :
    (∫ x in b..b+L, fluxDerivative u t x) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux u t) (f' := fluxDerivative u t) (a := b) (b := b+L)
    (fun x _ => flux_hasDerivAt u hu t x) (fluxDerivative_intervalIntegrable u hu b t)
  rw [flux_periodic u hu t b, sub_self] at h
  exact h

theorem densityDerivative_integral_eq_forcingWork (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    (∫ x in b..b+L, densityDerivative u t x) = ∫ x in b..b+L, forcingWork f u t x := by
  calc
    (∫ x in b..b+L, densityDerivative u t x) =
        ∫ x in b..b+L, fluxDerivative u t x + forcingWork f u t x :=
      intervalIntegral.integral_congr
        (fun x _ => densityDerivative_eq_fluxDerivative_add_forcingWork u hu hV t x)
    _ = (∫ x in b..b+L, fluxDerivative u t x) +
        ∫ x in b..b+L, forcingWork f u t x :=
      intervalIntegral.integral_add (fluxDerivative_intervalIntegrable u hu b t)
        (forcingWork_intervalIntegrable u hu hV b t)
    _ = ∫ x in b..b+L, forcingWork f u t x := by
      rw [fluxDerivative_integral_zero u hu b t, zero_add]

theorem energy_time_hasDerivAt_work (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V f u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) (∫ x in b..b+L, forcingWork f u t x) t := by
  have h := energy_time_hasDerivAt u hu b t
  rw [densityDerivative_integral_eq_forcingWork u hu hV b t] at h
  exact h

theorem energy_hasDerivAt_zero (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    HasDerivAt (energy u b L) 0 t := by
  simpa [forcingWork] using energy_time_hasDerivAt_work u hu hV b t

theorem energy_eq (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b s t : ℝ) :
    energy u b L s = energy u b L t :=
  is_const_of_deriv_eq_zero (f := energy u b L)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero u hu hV b r).deriv) s t

theorem energy_eq_initial (u : ℝ → ℝ → H)
    (hu : IsClassicalPeriodicSolution L V 0 u)
    (hV : ∀ t x, IsSelfAdjoint (V t x)) (b t : ℝ) :
    energy u b L t = energy u b L 0 :=
  energy_eq u hu hV b t 0

end NDEAEvolve.Exp013
