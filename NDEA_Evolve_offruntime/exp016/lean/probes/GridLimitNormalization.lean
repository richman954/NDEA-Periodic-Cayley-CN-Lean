import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology
namespace NDEAEvolve.Exp016.Probe
def mesh (G : ℕ → ℕ) (c : ℝ) (q : ℕ) : ℝ := c / (G q : ℝ)
theorem mesh_limit (G : ℕ → ℕ) (hG : Tendsto G atTop atTop) (c : ℝ) :
    Tendsto (mesh G c) atTop (𝓝 0) := by
  change Tendsto (fun q => mesh G c q) atTop (𝓝 0)
  have hi : Tendsto (fun q => (G q : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hG
  simpa only [mesh, div_eq_mul_inv, mul_zero] using hi.const_mul c
#print axioms mesh_limit
end NDEAEvolve.Exp016.Probe
