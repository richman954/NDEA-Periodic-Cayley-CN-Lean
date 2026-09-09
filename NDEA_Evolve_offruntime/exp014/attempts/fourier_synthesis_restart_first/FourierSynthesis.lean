import FourierPotential
import ScalarSeries
import StrongOperatorDerivative

/-! Synthesis and the actual spatial derivatives from the second-moment
Fourier state. All three evaluation maps are bounded, hence support joint
continuity along continuous state curves. -/
noncomputable section
open scoped BigOperators Topology
namespace NDEAEvolve.Exp014

def synthesisMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  character x m * ((weight m : ℂ)⁻¹)

def firstMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  (Complex.I * (m : ℂ)) * synthesisMultiplier x m

def secondMultiplier (x : ℝ) (m : ℤ) : ℂ :=
  (-(m : ℂ)^2) * synthesisMultiplier x m

theorem synthesisMultiplier_norm (x : ℝ) (m : ℤ) :
    ‖synthesisMultiplier x m‖ = (weight m)⁻¹ := by
  simp [synthesisMultiplier, norm_mul, character_norm, Complex.norm_real,
    Real.norm_eq_abs, (weight_pos m).le]

theorem synthesisMultiplier_bound (x : ℝ) (m : ℤ) :
    ‖synthesisMultiplier x m‖ ≤ 1 := by
  rw [synthesisMultiplier_norm]
  exact (inv_le_one₀ (weight_pos m)).mpr (weight_one_le m)

theorem firstMultiplier_bound (x : ℝ) (m : ℤ) : ‖firstMultiplier x m‖ ≤ 1 := by
  simpa [firstMultiplier, norm_mul, Complex.norm_intCast,
    synthesisMultiplier_norm, div_eq_mul_inv] using abs_frequency_div_weight_le m

theorem secondMultiplier_bound (x : ℝ) (m : ℤ) : ‖secondMultiplier x m‖ ≤ 1 := by
  simpa [secondMultiplier, norm_mul, norm_neg, norm_pow, Complex.norm_intCast,
    synthesisMultiplier_norm, sq_abs, div_eq_mul_inv] using frequency_sq_div_weight_le m

theorem synthesisMultiplier_continuous (m : ℤ) :
    Continuous (fun x => synthesisMultiplier x m) :=
  (character_continuous m).mul_const _

theorem firstMultiplier_continuous (m : ℤ) : Continuous (fun x => firstMultiplier x m) :=
  (synthesisMultiplier_continuous m).const_mul _

theorem secondMultiplier_continuous (m : ℤ) : Continuous (fun x => secondMultiplier x m) :=
  (synthesisMultiplier_continuous m).const_mul _

theorem synthesisMultiplier_hasDerivAt (x : ℝ) (m : ℤ) :
    HasDerivAt (fun y => synthesisMultiplier y m) (firstMultiplier x m) x := by
  simpa [synthesisMultiplier, firstMultiplier, mul_assoc] using
    (character_hasDerivAt m x).mul_const ((weight m : ℂ)⁻¹)

theorem firstMultiplier_hasDerivAt (x : ℝ) (m : ℤ) :
    HasDerivAt (fun y => firstMultiplier y m) (secondMultiplier x m) x := by
  have h := (synthesisMultiplier_hasDerivAt x m).const_mul (Complex.I * (m : ℂ))
  convert h using 1
  simp only [secondMultiplier, firstMultiplier]
  calc
    -(m : ℂ)^2 * synthesisMultiplier x m =
        Complex.I^2 * (m : ℂ)^2 * synthesisMultiplier x m := by rw [Complex.I_sq]; ring
    _ = _ := by ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def synthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (synthesisMultiplier x) (synthesisMultiplier_bound x)

def firstSynthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (firstMultiplier x) (firstMultiplier_bound x)

def secondSynthesisCLM (x : ℝ) : FourierState H →L[ℂ] H :=
  scalarSeriesCLM (secondMultiplier x) (secondMultiplier_bound x)

def synth (b : FourierState H) (x : ℝ) : H := synthesisCLM x b

def synthFirst (b : FourierState H) (x : ℝ) : H := firstSynthesisCLM x b

def synthSecond (b : FourierState H) (x : ℝ) : H := secondSynthesisCLM x b

theorem synth_eq_tsum (b : FourierState H) (x : ℝ) :
    synth b x = ∑' m, character x m • coefficient b m := by
  change (∑' m, synthesisMultiplier x m • b m) = _
  apply tsum_congr
  intro m
  simp [synthesisMultiplier, coefficient, smul_smul]

theorem synth_norm_le (b : FourierState H) (x : ℝ) : ‖synth b x‖ ≤ ‖b‖ :=
  scalarSeries_norm_le (synthesisMultiplier x) (synthesisMultiplier_bound x) b

theorem synth_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synth p.2 p.1) :=
  scalarSeries_joint_continuous synthesisMultiplier synthesisMultiplier_bound
    synthesisMultiplier_continuous

theorem synthFirst_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synthFirst p.2 p.1) :=
  scalarSeries_joint_continuous firstMultiplier firstMultiplier_bound firstMultiplier_continuous

theorem synthSecond_joint_continuous :
    Continuous (fun p : ℝ × FourierState H => synthSecond p.2 p.1) :=
  scalarSeries_joint_continuous secondMultiplier secondMultiplier_bound secondMultiplier_continuous

theorem synth_hasDerivAt (b : FourierState H) (x : ℝ) :
    HasDerivAt (synth b) (synthFirst b x) x :=
  scalarSeries_hasDerivAt synthesisMultiplier firstMultiplier synthesisMultiplier_bound
    firstMultiplier_bound synthesisMultiplier_hasDerivAt b x

theorem synthFirst_hasDerivAt (b : FourierState H) (x : ℝ) :
    HasDerivAt (synthFirst b) (synthSecond b x) x :=
  scalarSeries_hasDerivAt firstMultiplier secondMultiplier firstMultiplier_bound
    secondMultiplier_bound firstMultiplier_hasDerivAt b x

theorem synth_periodic (b : FourierState H) : Function.Periodic (synth b) (2 * Real.pi) := by
  intro x
  simp only [synth_eq_tsum]
  apply tsum_congr
  intro m
  have hp : character (x + 2 * Real.pi) m = character x m := character_periodic m x
  rw [hp]

def freeMultiplier (t x : ℝ) (m : ℤ) : ℂ := phase t m * synthesisMultiplier x m

def freeDerivativeMultiplier (t x : ℝ) (m : ℤ) : ℂ :=
  Complex.I * (phase t m * secondMultiplier x m)

theorem freeMultiplier_bound (t x : ℝ) (m : ℤ) : ‖freeMultiplier t x m‖ ≤ 1 := by
  simpa [freeMultiplier, norm_mul, phase_norm] using synthesisMultiplier_bound x m

theorem freeDerivativeMultiplier_bound (t x : ℝ) (m : ℤ) :
    ‖freeDerivativeMultiplier t x m‖ ≤ 1 := by
  simpa [freeDerivativeMultiplier, norm_mul, phase_norm] using secondMultiplier_bound x m

theorem freeMultiplier_hasDerivAt (t x : ℝ) (m : ℤ) :
    HasDerivAt (fun s => freeMultiplier s x m) (freeDerivativeMultiplier t x m) t := by
  have h := (phase_hasDerivAt t m).mul_const (synthesisMultiplier x m)
  convert h using 1
  simp only [freeDerivativeMultiplier, secondMultiplier]
  ring

theorem freeMultiplier_series (b : FourierState H) (t x : ℝ) :
    scalarSeries (freeMultiplier t x) b = synth (freeFlow t b) x := by
  change (∑' m, freeMultiplier t x m • b m) =
    ∑' m, synthesisMultiplier x m • freeFlow t b m
  apply tsum_congr
  intro m
  simp [freeMultiplier, freeFlow_apply, smul_smul, mul_comm]

theorem freeDerivativeMultiplier_series (b : FourierState H) (t x : ℝ) :
    scalarSeries (freeDerivativeMultiplier t x) b = Complex.I • synthSecond (freeFlow t b) x := by
  rw [scalarSeries]
  change (∑' m, freeDerivativeMultiplier t x m • b m) =
    Complex.I • ∑' m, secondMultiplier x m • freeFlow t b m
  rw [← (scalarSeries_summable (secondMultiplier x) (secondMultiplier_bound x) (freeFlow t b)).tsum_const_smul]
  apply tsum_congr
  intro m
  simp [freeDerivativeMultiplier, freeFlow_apply, smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem synth_freeFlow_hasDerivAt (b : FourierState H) (t x : ℝ) :
    HasDerivAt (fun s => synth (freeFlow s b) x)
      (Complex.I • synthSecond (freeFlow t b) x) t := by
  have h := scalarSeries_hasDerivAt (fun s => freeMultiplier s x)
    (fun s => freeDerivativeMultiplier s x)
    (fun s => freeMultiplier_bound s x) (fun s => freeDerivativeMultiplier_bound s x)
    (fun s => freeMultiplier_hasDerivAt s x) b t
  simpa only [freeMultiplier_series, freeDerivativeMultiplier_series] using h

end NDEAEvolve.Exp014
