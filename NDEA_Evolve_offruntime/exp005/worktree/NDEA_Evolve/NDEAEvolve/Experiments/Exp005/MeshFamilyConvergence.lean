import NDEAEvolve.Experiments.Exp005.SymmetricStageResidual

/-!
# Conditional convergence of mesh-weighted errors on varying finite spaces

The dimensions and Hermitian matrices may depend on the refinement index.
The conclusion is convergence of the scalar weighted error; it does not
identify different finite-dimensional state spaces or assert convergence of
interpolants in a common function space. Uniform residual bounds remain
explicit premises, not consequences of stability or of fixed-matrix Exp004.
-/

noncomputable section

open Filter
open scoped Topology
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004

namespace NDEAEvolve.Exp005

/-- A common space-time residual majorant vanishes under mesh refinement. -/
theorem mesh_error_majorant_tendsto_zero
    (k dx initial : ℕ → ℝ) (T Ct Cs : ℝ)
    (hk : Tendsto k atTop (𝓝 0)) (hdx : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto initial atTop (𝓝 0)) :
    Tendsto (fun q => initial q + T * (Ct * k q ^ 2 + Cs * dx q ^ 2))
      atTop (𝓝 0) := by
  simpa using hinitial.add
    ((tendsto_const_nhds (x := T)).mul
      (((tendsto_const_nhds (x := Ct)).mul (hk.pow 2)).add
        ((tendsto_const_nhds (x := Cs)).mul (hdx.pow 2))))

/-- Conditional mesh-family convergence from the actual trajectory defects.
The constants Ct, Cs, T are common across all refinement indices; generator
norms and dimensions are unrestricted. Physical spacings are positive. -/
theorem symmetric_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (dx k : ℕ → ℝ) (T Ct Cs : ℝ)
    (A B : (q : ℕ) → Mat (n q))
    (hA : ∀ q, (A q).IsHermitian) (hB : ∀ q, (B q).IsHermitian)
    (u v : (q : ℕ) → ℕ → E (n q))
    (hv : ∀ q j, v q (j + 1) = symmetricStepHat (A q) (B q) (k q) (v q j))
    (hdx : ∀ q, 0 < dx q) (hk : ∀ q, 0 ≤ k q)
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : ∀ q, (N q : ℝ) * k q ≤ T)
    (hdefect : ∀ q j, j < N q →
      weightedNorm (dx q) (trajectoryDefect (A q) (B q) (k q) (u q) j) ≤
        k q * (Ct * k q ^ 2 + Cs * dx q ^ 2))
    (hk_limit : Tendsto k atTop (𝓝 0)) (hdx_limit : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto (fun q => weightedNorm (dx q) (u q 0 - v q 0))
      atTop (𝓝 0)) :
    Tendsto (fun q => weightedNorm (dx q) (u q (N q) - v q (N q)))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun q => weightedNorm_nonneg (dx q) (u q (N q) - v q (N q)))
  · intro q
    exact symmetric_weighted_fixed_time_error (dx q) (k q) T Ct Cs
      (A q) (B q) (hA q) (hB q) (u q) (v q) (hv q) (N q)
      (hk q) hCt hCs (horizon q) (hdefect q)
  · exact mesh_error_majorant_tendsto_zero k dx _ T Ct Cs
      hk_limit hdx_limit hinitial

/-- Conditional convergence using the three measured factor residuals of
the actual symmetric Cayley stages. This is the PDE-facing transfer endpoint;
deriving its uniform hbudget premise for a smooth split PDE is separate work. -/
theorem symmetric_stage_mesh_family_error_tendsto_zero
    (n N : ℕ → ℕ) (dx k : ℕ → ℝ) (T Ct Cs : ℝ)
    (A B : (q : ℕ) → Mat (n q))
    (hA : ∀ q, (A q).IsHermitian) (hB : ∀ q, (B q).IsHermitian)
    (u v first second : (q : ℕ) → ℕ → E (n q))
    (hv : ∀ q j, v q (j + 1) = symmetricStepHat (A q) (B q) (k q) (v q j))
    (hdx : ∀ q, 0 < dx q) (hk : ∀ q, 0 ≤ k q)
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (horizon : ∀ q, (N q : ℝ) * k q ≤ T)
    (hbudget : ∀ q j, j < N q →
      stageResidualBudget (dx q) (k q) (A q) (B q)
        (u q j) (first q j) (second q j) (u q (j + 1)) ≤
          k q * (Ct * k q ^ 2 + Cs * dx q ^ 2))
    (hk_limit : Tendsto k atTop (𝓝 0)) (hdx_limit : Tendsto dx atTop (𝓝 0))
    (hinitial : Tendsto (fun q => weightedNorm (dx q) (u q 0 - v q 0))
      atTop (𝓝 0)) :
    Tendsto (fun q => weightedNorm (dx q) (u q (N q) - v q (N q)))
      atTop (𝓝 0) := by
  apply symmetric_mesh_family_error_tendsto_zero n N dx k T Ct Cs A B hA hB
    u v hv hdx hk hCt hCs horizon
  · intro q j hj
    exact (symmetric_stage_residual_weighted_le (dx q) (k q) (A q) (B q)
      (hA q) (hB q) (u q j) (first q j) (second q j) (u q (j + 1))).trans
        (hbudget q j hj)
  · exact hk_limit
  · exact hdx_limit
  · exact hinitial

end NDEAEvolve.Exp005

#check @NDEAEvolve.Exp005.symmetric_mesh_family_error_tendsto_zero
#check @NDEAEvolve.Exp005.symmetric_stage_mesh_family_error_tendsto_zero
#print axioms NDEAEvolve.Exp005.mesh_error_majorant_tendsto_zero
#print axioms NDEAEvolve.Exp005.symmetric_mesh_family_error_tendsto_zero
#print axioms NDEAEvolve.Exp005.symmetric_stage_mesh_family_error_tendsto_zero
