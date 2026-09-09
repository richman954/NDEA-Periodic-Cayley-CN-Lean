import Reconstruction
import ScheduleBounds
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform convergence of the actual reconstructed fields over one closed
space-time rectangle, to the classical periodic spinor solution. -/
noncomputable section
open Filter
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

def spaceTimeDomain : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2*Real.pi)

def scheduledReconstruction (q : ℕ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  reconstruction (gridIndex q) (mesh q) (timeStep q) (stepCount q) a t x

def uniformBound (q : ℕ) (a : ℤ → E 2) : ℝ :=
  nodalBound q a + moment 2 a*mesh q + 2*moment 2 a*timeStep q

theorem uniformBound_nonneg (q : ℕ) (a : ℤ → E 2) : 0 ≤ uniformBound q a :=
  add_nonneg (add_nonneg (nodalBound_nonneg q a)
    (mul_nonneg (moment_nonneg 2 a) (mesh_pos q).le))
    (mul_nonneg (mul_nonneg (by norm_num) (moment_nonneg 2 a)) (timeStep_nonneg q))

theorem uniformBound_tendsto_zero (a : ℤ → E 2) :
    Tendsto (fun q => uniformBound q a) atTop (nhds 0) := by
  simpa [uniformBound] using ((nodalBound_tendsto_zero a).add
    (mesh_tendsto_zero.const_mul (moment 2 a))).add
      (timeStep_tendsto_zero.const_mul (2*moment 2 a))

theorem scheduled_reconstruction_error_bound (q : ℕ) (a : ℤ → E 2) (ha : Regular a)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    ‖scheduledReconstruction q a t x-infiniteSolution a t x‖ ≤ uniformBound q a := by
  have hL : x ≤ ((gridIndex q+1:ℕ):ℝ)*mesh q := by rw [mesh_period]; exact hx.2
  have hT : t ≤ (stepCount q:ℝ)*timeStep q := by rw [stepCount_timeStep]; exact ht.2
  have hb := reconstruction_error_bound (gridIndex q) (mesh q) (timeStep q) (stepCount q)
    a ha t x (mesh_pos q) (timeStep_pos q) hx.1 hL ht.1 hT
  have hn := all_steps_nodal_bound q (timeIndex (stepCount q) (timeStep q) t)
    (timeIndex_le _ _ _) a ha
  exact hb.trans (add_le_add (add_le_add hn (le_refl _)) (le_refl _))

theorem reconstruction_tendstoUniformlyOn (a : ℤ → E 2) (ha : Regular a) :
    TendstoUniformlyOn (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution a p.1 p.2) atTop spaceTimeDomain := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hb : ∀ᶠ q in atTop, uniformBound q a < ε :=
    (uniformBound_tendsto_zero a).eventually (gt_mem_nhds hε)
  filter_upwards [hb] with q hq
  intro p hp
  have he := scheduled_reconstruction_error_bound q a ha p.1 p.2 hp.1 hp.2
  rw [dist_eq_norm, norm_sub_rev]
  exact he.trans_lt hq

theorem classical_uniform_reconstruction (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (infiniteSolution a) ∧
    TendstoUniformlyOn (fun q (p : ℝ × ℝ) => scheduledReconstruction q a p.1 p.2)
      (fun p : ℝ × ℝ => infiniteSolution a p.1 p.2) atTop spaceTimeDomain :=
  ⟨infiniteSolution_classical a ha, reconstruction_tendstoUniformlyOn a ha⟩

theorem reconstruction_at_point_tendsto (a : ℤ → E 2) (ha : Regular a)
    (t x : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    Tendsto (fun q => scheduledReconstruction q a t x) atTop
      (nhds (infiniteSolution a t x)) :=
  (reconstruction_tendstoUniformlyOn a ha).tendsto_at (x := (t,x)) ⟨ht,hx⟩

end NDEAEvolve.Exp011
