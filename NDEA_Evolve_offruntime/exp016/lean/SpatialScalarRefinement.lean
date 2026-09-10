import WeightedSpatialMoments

/-! Explicit scalar refinement for the actual spatial certificate.
The low cutoff expands inside the full odd grid. Potential tails use only
Exp014's original second weighted absolute moment. The generator growth is
controlled by the saved N^-4 time step; no numerical regularity is assumed here.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
namespace NDEAEvolve.Exp016

def spatialLowCutoff (q : ℕ) : ℕ := initialSamplingCutoff q / 2

theorem spatialLowCutoff_le (q : ℕ) : spatialLowCutoff q ≤ initialSamplingCutoff q :=
  Nat.div_le_self _ _

theorem spatialLowCutoff_tendsto_atTop : Tendsto spatialLowCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨2 * b, fun q hq => by
    unfold spatialLowCutoff initialSamplingCutoff
    omega⟩

theorem spatialCutoffGap_tendsto_atTop :
    Tendsto (fun q => initialSamplingCutoff q - spatialLowCutoff q) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨2 * b, fun q hq => by
    unfold spatialLowCutoff initialSamplingCutoff
    omega⟩

/-- The already proved weighted tail bound now yields an actual limit. -/
theorem frequencyNormTail_tendsto_zero {F : Type*} [NormedAddCommGroup F]
    (f : ℤ → F) (hf : Summable (fun j => ‖f j‖))
    (hw : Summable (fun j => Exp014.weight j * ‖f j‖))
    (L : ℕ → ℕ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun q => frequencyNormTail f (L q)) atTop (𝓝 0) := by
  have hi : Tendsto (fun q => (1 + (L q : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_comm] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        ((tendsto_add_atTop_nat 1).comp hL)
  have hm : Tendsto (fun q => (∑' j, Exp014.weight j * ‖f j‖) /
      (1 + (L q : ℝ))^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (hi.pow 2).const_mul (∑' j, Exp014.weight j * ‖f j‖)
  exact squeeze_zero (fun q => frequencyNormTail_nonneg f (L q))
    (fun q => frequencyNormTail_le_weighted f hf hw (L q)) hm

theorem initialSamplingMesh_tendsto_zero : Tendsto initialSamplingMesh atTop (𝓝 0) := by
  change Tendsto (fun q => initialSamplingMesh q) atTop (𝓝 0)
  have hi : Tendsto (fun q => (temporalGridSize q : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp temporalGridSize_tendsto_atTop
  simpa only [initialSamplingMesh, temporalGridSize, div_eq_mul_inv, mul_zero] using
    hi.const_mul (2 * Real.pi)

/-- Complete stencil and low/high potential coefficient in the physical L2 budget. -/
theorem spatialFourthWeightCoefficient_tendsto_zero
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) :
    Tendsto (fun q => spatialFourthWeightCoefficient (initialSamplingCutoff q)
      (spatialLowCutoff q) (initialSamplingMesh q) v) atTop (𝓝 0) := by
  have ht := frequencyNormTail_tendsto_zero v (Exp014.regularPotential_absolute v hv) hv
    (fun q => initialSamplingCutoff q - spatialLowCutoff q) spatialCutoffGap_tendsto_atTop
  have hi : Tendsto (fun q => (1 + (spatialLowCutoff q : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_comm] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        ((tendsto_add_atTop_nat 1).comp spatialLowCutoff_tendsto_atTop)
  have ha : Tendsto (fun q => (∑' ell, ‖v ell‖) / (1 + (spatialLowCutoff q : ℝ))^4)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 4 ≠ 0), mul_zero] using
      (hi.pow 4).const_mul (∑' ell, ‖v ell‖)
  have hh := (initialSamplingMesh_tendsto_zero.pow 2).const_mul (Real.sqrt (2 * Real.pi))
  simpa only [spatialFourthWeightCoefficient, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero] using hh.add ((ht.add ha).const_mul (2 * Real.sqrt (2 * Real.pi)))

/-- Exact rescaling, retaining both the kinetic and potential generator terms. -/
theorem temporalStep_generatorCoefficient_rescaled (n K : ℝ) (hn : n ≠ 0) :
    (n^4)⁻¹ * (4 / (2 * Real.pi / n)^2 + K) =
      (Real.pi⁻¹)^2 * (n⁻¹)^2 + K * (n⁻¹)^4 := by
  field_simp [hn, Real.pi_ne_zero]
  ring

theorem scheduledStep_generatorCoefficient_tendsto_zero (K : ℝ) :
    Tendsto (fun q => temporalStepSize q * (4 / (initialSamplingMesh q)^2 + K))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun q => (temporalGridSize q : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp temporalGridSize_tendsto_atTop
  have hz := ((hi.pow 2).const_mul ((Real.pi⁻¹)^2)).add ((hi.pow 4).const_mul K)
  simp only [zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), mul_zero,
    add_zero] at hz
  convert hz using 1
  funext q
  have hn : (temporalGridSize q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (temporalGridSize_pos q))
  simpa only [temporalStepSize, temporalStepCount, Nat.cast_pow,
    initialSamplingMesh, temporalGridSize] using
    temporalStep_generatorCoefficient_rescaled (temporalGridSize q : ℝ) K hn

#print axioms spatialLowCutoff_le
#print axioms spatialLowCutoff_tendsto_atTop
#print axioms spatialCutoffGap_tendsto_atTop
#print axioms frequencyNormTail_tendsto_zero
#print axioms initialSamplingMesh_tendsto_zero
#print axioms spatialFourthWeightCoefficient_tendsto_zero
#print axioms temporalStep_generatorCoefficient_rescaled
#print axioms scheduledStep_generatorCoefficient_tendsto_zero
end NDEAEvolve.Exp016
