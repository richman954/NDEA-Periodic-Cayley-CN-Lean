import EnergyLocal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Energy conservation for every classical periodic solution, on a period
interval with arbitrary real base point. A local compact rectangle supplies
the domination required to differentiate the integral; there is no additional
global bound or Fourier representation assumption. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp012

theorem compact_derivative_bound (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b t : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Ioo (t-1) (t+1), ∀ x ∈ uIcc a b, ‖g s x‖≤C := by
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

def energy (u : ℝ → ℝ → E 2) (b t : ℝ) : ℝ :=
  ∫ x in b..b+2*Real.pi, ‖u t x‖^2

theorem energy_intervalIntegrable (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    IntervalIntegrable (fun x => ‖u t x‖^2) volume b (b+2*Real.pi) := by
  have hc : Continuous (energyDensity u t) :=
    (energyDensity_continuous u hu).comp (f := fun x : ℝ => (t,x))
      (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable b (b+2*Real.pi)

theorem densityDerivative_intervalIntegrable (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    IntervalIntegrable (densityDerivative u t) volume b (b+2*Real.pi) := by
  have hc : Continuous (densityDerivative u t) :=
    (densityDerivative_continuous u hu).comp (f := fun x : ℝ => (t,x))
      (continuous_const.prodMk continuous_id)
  exact hc.intervalIntegrable b (b+2*Real.pi)

theorem energy_time_hasDerivAt (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    HasDerivAt (energy u b) (∫ x in b..b+2*Real.pi, densityDerivative u t x) t :=
  joint_interval_hasDerivAt (energyDensity u) (densityDerivative u)
    (energyDensity_continuous u hu) (densityDerivative_continuous u hu)
    (density_time_hasDerivAt u hu) b (b+2*Real.pi) t

theorem densityDerivative_integral_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    (∫ x in b..b+2*Real.pi, densityDerivative u t x)=0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux u t) (f' := densityDerivative u t) (a := b) (b := b+2*Real.pi)
    (fun x _ => flux_hasDerivAt u hu t x) (densityDerivative_intervalIntegrable u hu b t)
  rw [flux_periodic u hu t b, sub_self] at h
  exact h

theorem energy_hasDerivAt_zero (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    HasDerivAt (energy u b) 0 t := by
  have h := energy_time_hasDerivAt u hu b t
  rw [densityDerivative_integral_zero u hu b t] at h
  exact h

theorem energy_eq (u : ℝ → ℝ → E 2) (hu : IsClassicalPeriodicSolution u)
    (b s t : ℝ) : energy u b s=energy u b t :=
  is_const_of_deriv_eq_zero
    (f := energy u b)
    (fun r => (energy_hasDerivAt_zero u hu b r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero u hu b r).deriv) s t

theorem energy_eq_initial (u : ℝ → ℝ → E 2)
    (hu : IsClassicalPeriodicSolution u) (b t : ℝ) :
    energy u b t=energy u b 0 :=
  energy_eq u hu b t 0

end NDEAEvolve.Exp012
