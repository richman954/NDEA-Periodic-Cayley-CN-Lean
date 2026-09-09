import Exp005Foundation
import PeriodicModeResidual
import PeriodicGrid

/-! Discharge Exp005's actual implicit-factor residual budget on a concrete
nonconstant periodic split-Schrodinger solution and the real cyclic stencil. -/
noncomputable section
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp005
namespace NDEAEvolve.Exp006

def sampleState (n : ℕ) (h s : ℝ) : E (n+1) :=
  WithLp.toLp 2 (PeriodicGrid.sample h (fun x => phase (x-s)))

theorem shifted_phase_periodic (s : ℝ) :
    Function.Periodic (fun x => phase (x-s)) (2*Real.pi) := by
  intro x
  change phase (x+2*Real.pi-s) = phase (x-s)
  rw [show x+2*Real.pi-s = (x-s)+2*Real.pi by ring]
  exact phase_periodic (x-s)

theorem sampled_laplacian_eigen (n : ℕ) (h s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi) (i : Fin (n+1)) :
    (PeriodicGrid.laplacian n h).mulVec (WithLp.ofLp (sampleState n h s)) i =
      (spatialSymbol h : ℂ) * phase ((i.val : ℝ)*h-s) := by
  change (PeriodicGrid.laplacian n h).mulVec
    (PeriodicGrid.sample h (fun x => phase (x-s))) i = _
  rw [PeriodicGrid.matrix_sample_stencil (2*Real.pi) h _
    (shifted_phase_periodic s) hmesh]
  rw [show (i.val : ℝ)*h+h-s = ((i.val : ℝ)*h-s)+h by ring,
    show (i.val : ℝ)*h-h-s = ((i.val : ℝ)*h-s)-h by ring]
  exact phase_centeredStencil h ((i.val : ℝ)*h-s)

theorem factorResidual_component {n : ℕ} (H : Mat n) (a : ℝ)
    (u v : E n) (i : Fin n) :
    WithLp.ofLp (factorResidual H a u v) i =
      (WithLp.ofLp v i + Complex.I*(a : ℂ)*(H.mulVec (WithLp.ofLp v) i)) -
      (WithLp.ofLp u i - Complex.I*(a : ℂ)*(H.mulVec (WithLp.ofLp u) i)) := by
  change (cayleyD a H).mulVec (WithLp.ofLp v) i -
    (cayleyN a H).mulVec (WithLp.ofLp u) i = _
  simp [cayleyD, cayleyN, skewPart, cscalar, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec]

theorem actual_factorResidual_component (n : ℕ) (h a s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi) (i : Fin (n+1)) :
    WithLp.ofLp (factorResidual (PeriodicGrid.laplacian n h) a
      (sampleState n h s) (sampleState n h (s+2*a))) i =
      scalarFactorResidual h a ((i.val : ℝ)*h-s) := by
  rw [factorResidual_component, sampled_laplacian_eigen n h (s+2*a) hmesh,
    sampled_laplacian_eigen n h s hmesh]
  change (phase ((i.val : ℝ)*h-(s+2*a)) + _ ) -
    (phase ((i.val : ℝ)*h-s) - _) = _
  rw [show (i.val : ℝ)*h-(s+2*a) = ((i.val : ℝ)*h-s)-2*a by ring]
  unfold scalarFactorResidual
  ring

theorem actual_factorResidual_weighted_bound (n : ℕ) (h a s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    weightedNorm h (factorResidual (PeriodicGrid.laplacian n h) a
      (sampleState n h s) (sampleState n h (s+2*a))) ≤
      Real.sqrt (2*Real.pi) * (2*a^3+a*h^2/4) := by
  let r := factorResidual (PeriodicGrid.laplacian n h) a
    (sampleState n h s) (sampleState n h (s+2*a))
  have hb := weightedNorm_of_pointwise_bound h (2*Real.pi) (2*a^3+a*h^2/4)
    hh.le (by positivity) hmesh (WithLp.ofLp r) (by positivity)
    (fun i => by
      dsimp [r]
      rw [actual_factorResidual_component n h a s hmesh]
      exact scalarFactorResidual_bound h a _ hh hhsmall ha hasmall)
  simpa only [WithLp.toLp_ofLp] using hb

/-- The exact Exp005 budget premise, now derived for concrete cyclic matrices.
No residual, regularity, or generator-norm hypothesis is supplied. -/
theorem actual_stageResidualBudget_bound (n : ℕ) (h k s : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 2) :
    stageResidualBudget h k (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h)
      (sampleState n h s) (sampleState n h (s+k/2))
      (sampleState n h (s+3*k/2)) (sampleState n h (s+2*k)) ≤
      k * (((5/16 : ℝ)*Real.sqrt (2*Real.pi))*k^2 +
        ((1/4 : ℝ)*Real.sqrt (2*Real.pi))*h^2) := by
  have h1 := actual_factorResidual_weighted_bound n h (k/4) s hmesh hh hhsmall
    (by positivity) (by linarith)
  have h2 := actual_factorResidual_weighted_bound n h (k/2) (s+k/2) hmesh hh hhsmall
    (by positivity) (by linarith)
  have h3 := actual_factorResidual_weighted_bound n h (k/4) (s+3*k/2) hmesh hh hhsmall
    (by positivity) (by linarith)
  rw [show s+2*(k/4)=s+k/2 by ring] at h1
  rw [show s+k/2+2*(k/2)=s+3*k/2 by ring] at h2
  rw [show s+3*k/2+2*(k/4)=s+2*k by ring] at h3
  unfold stageResidualBudget
  calc
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The physical reference trajectory is exactly samples of U(j*k,x). -/
def reference (n : ℕ) (h k : ℝ) (j : ℕ) : E (n+1) :=
  sampleState n h (2*(j : ℝ)*k)

theorem reference_is_sampled_mode (n : ℕ) (h k : ℝ) (j : ℕ) (i : Fin (n+1)) :
    WithLp.ofLp (reference n h k j) i = mode ((j : ℝ)*k) ((i.val : ℝ)*h) := by
  change phase ((i.val : ℝ)*h-(2*(j : ℝ)*k)) =
    phase ((i.val : ℝ)*h-2*((j : ℝ)*k))
  congr 1
  ring

/-- Exp005's fixed-time theorem specialized with its formerly assumed budget
discharged. Constants are uniform over all admissible finite periodic meshes. -/
theorem concrete_periodic_fixed_time_error (n : ℕ) (h k T : ℝ)
    (hmesh : ((n+1 : ℕ) : ℝ) * h = 2*Real.pi)
    (hh : 0 < h) (hhsmall : h ≤ 1) (hk : 0 ≤ k) (hksmall : k ≤ 2)
    (v : ℕ → E (n+1))
    (hv : ∀ j, v (j+1) = symmetricStepHat
      (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h) k (v j))
    (N : ℕ) (horizon : (N : ℝ)*k ≤ T) :
    weightedNorm h (reference n h k N-v N) ≤
      weightedNorm h (reference n h k 0-v 0) +
      T*(((5/16 : ℝ)*Real.sqrt (2*Real.pi))*k^2 +
        ((1/4 : ℝ)*Real.sqrt (2*Real.pi))*h^2) := by
  apply symmetric_stage_residual_fixed_time_error h k T
    ((5/16 : ℝ)*Real.sqrt (2*Real.pi)) ((1/4 : ℝ)*Real.sqrt (2*Real.pi))
    (PeriodicGrid.laplacian n h) (PeriodicGrid.laplacian n h)
    (PeriodicGrid.isHermitian n h) (PeriodicGrid.isHermitian n h)
    (reference n h k) v
    (fun j => sampleState n h (2*(j : ℝ)*k+k/2))
    (fun j => sampleState n h (2*(j : ℝ)*k+3*k/2))
    hv N hk (by positivity) (by positivity) horizon
  intro j _hj
  have hb := actual_stageResidualBudget_bound n h k (2*(j : ℝ)*k)
    hmesh hh hhsmall hk hksmall
  have hnext : 2*((j+1 : ℕ) : ℝ)*k = 2*(j : ℝ)*k+2*k := by push_cast; ring
  simpa only [reference, hnext] using hb

/-- Across varying physical grids the scalar weighted error tends to zero.
Terminal times satisfy N_q*k_q≤T; no equality to T is silently imposed. -/
theorem concrete_periodic_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (h k : ℕ → ℝ) (T : ℝ)
    (hmesh : ∀ q, ((n q+1 : ℕ) : ℝ)*h q = 2*Real.pi)
    (hh : ∀ q, 0 < h q) (hhsmall : ∀ q, h q ≤ 1)
    (hk : ∀ q, 0 ≤ k q) (hksmall : ∀ q, k q ≤ 2)
    (v : (q : ℕ) → ℕ → E (n q+1))
    (hv : ∀ q j, v q (j+1) = symmetricStepHat
      (PeriodicGrid.laplacian (n q) (h q)) (PeriodicGrid.laplacian (n q) (h q))
        (k q) (v q j))
    (horizon : ∀ q, (N q : ℝ)*k q ≤ T)
    (hk_limit : Filter.Tendsto k Filter.atTop (nhds 0))
    (hh_limit : Filter.Tendsto h Filter.atTop (nhds 0))
    (hinitial : Filter.Tendsto
      (fun q => weightedNorm (h q) (reference (n q) (h q) (k q) 0-v q 0))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun q => weightedNorm (h q) (reference (n q) (h q) (k q) (N q)-v q (N q)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun q => weightedNorm_nonneg (h q) _)
  · intro q
    exact concrete_periodic_fixed_time_error (n q) (h q) (k q) T
      (hmesh q) (hh q) (hhsmall q) (hk q) (hksmall q) (v q) (hv q)
      (N q) (horizon q)
  · exact mesh_error_majorant_tendsto_zero k h _ T
      ((5/16 : ℝ)*Real.sqrt (2*Real.pi)) ((1/4 : ℝ)*Real.sqrt (2*Real.pi))
      hk_limit hh_limit hinitial

#print axioms sampled_laplacian_eigen
#print axioms actual_factorResidual_component
#print axioms actual_factorResidual_weighted_bound
#print axioms actual_stageResidualBudget_bound
#print axioms concrete_periodic_fixed_time_error
#print axioms concrete_periodic_mesh_family_error_tendsto_zero
end NDEAEvolve.Exp006
