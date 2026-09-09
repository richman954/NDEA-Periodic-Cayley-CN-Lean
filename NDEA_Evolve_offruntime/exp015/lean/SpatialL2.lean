import GenericEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt

/-! Spatial L2 size and the Cauchy--Schwarz estimate for actual forcing work.
The real integral inequality follows from positivity of integrated squares;
no unproved integral estimate is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Topology Interval
namespace NDEAEvolve.Exp015

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spatialL2 (u : ℝ → H) (b L : ℝ) : ℝ :=
  Real.sqrt (∫ x in b..b+L, ‖u x‖ ^ 2)

theorem spatialL2_nonneg (u : ℝ → H) (b L : ℝ) : 0 ≤ spatialL2 u b L :=
  Real.sqrt_nonneg _

theorem spatialL2_sq (u : ℝ → H) (b L : ℝ) (hL : 0 ≤ L) :
    spatialL2 u b L ^ 2 = ∫ x in b..b+L, ‖u x‖ ^ 2 := by
  apply Real.sq_sqrt
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun x => sq_nonneg _)

theorem spatialL2_sq_eq_energy (u : ℝ → ℝ → H) (b L t : ℝ) (hL : 0 ≤ L) :
    spatialL2 (u t) b L ^ 2 = Exp013.energy u b L t :=
  spatialL2_sq (u t) b L hL

theorem energy_nonneg (u : ℝ → ℝ → H) (b L t : ℝ) (hL : 0 ≤ L) :
    0 ≤ Exp013.energy u b L t := by
  rw [← spatialL2_sq_eq_energy u b L t hL]
  exact sq_nonneg _

@[simp] theorem spatialL2_zero (b L : ℝ) : spatialL2 (0 : ℝ → H) b L = 0 := by
  simp [spatialL2]

theorem spatialL2_const (c : H) (b L : ℝ) (hL : 0 ≤ L) :
    spatialL2 (fun _ : ℝ => c) b L = Real.sqrt L * ‖c‖ := by
  simp only [spatialL2, intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]
  rw [Real.sqrt_mul hL, Real.sqrt_sq (norm_nonneg c)]

private theorem spatial_joint_integral_continuous (g : ℝ → ℝ → ℝ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) (a b : ℝ) :
    Continuous (fun t => ∫ x in a..b, g t x) := by
  have hc (c d : ℝ) : Continuous (fun t => ∫ x in Icc c d, g t x) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  have hi (c d : ℝ) : Continuous (fun t => ∫ x in Ioc c d, g t x) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hc c d
  exact (hi a b).sub (hi b a)

theorem spatialL2_time_continuous (u : ℝ → ℝ → H)
    (hu : Continuous (fun p : ℝ × ℝ => u p.1 p.2)) (b L : ℝ) :
    Continuous (fun t => spatialL2 (u t) b L) :=
  Real.continuous_sqrt.comp
    (spatial_joint_integral_continuous (fun t x => ‖u t x‖ ^ 2) (hu.norm.pow 2) b (b+L))

private theorem spatial_integral_cauchy_schwarz (p q : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, p x * q x) ≤
      Real.sqrt (∫ x in a..b, p x ^ 2) * Real.sqrt (∫ x in a..b, q x ^ 2) := by
  let A := ∫ x in a..b, p x ^ 2
  let B := ∫ x in a..b, q x ^ 2
  let C := ∫ x in a..b, p x * q x
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)
  have hquad (r : ℝ) : 0 ≤ B * (r*r) + (-2*C)*r + A := by
    have hn : 0 ≤ ∫ x in a..b, (p x - r*q x)^2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun x => sq_nonneg _)
    have he : (fun x => (p x - r*q x)^2) =
        (fun x => (p x)^2 - (2*r)*(p x*q x) + r^2*(q x)^2) := by
      funext x
      ring
    have hp2 : IntervalIntegrable (fun x => p x ^ 2) volume a b :=
      (hp.pow 2).intervalIntegrable a b
    have hrpq : IntervalIntegrable (fun x => (2*r)*(p x*q x)) volume a b :=
      ((hp.mul hq).const_mul (2*r)).intervalIntegrable a b
    have hrq2 : IntervalIntegrable (fun x => r^2*(q x)^2) volume a b :=
      ((hq.pow 2).const_mul (r^2)).intervalIntegrable a b
    rw [he, intervalIntegral.integral_add (f := fun x => p x ^ 2 - (2*r)*(p x*q x))
      (g := fun x => r^2*(q x)^2) (hp2.sub hrpq) hrq2,
      intervalIntegral.integral_sub (f := fun x => p x ^ 2)
        (g := fun x => (2*r)*(p x*q x)) hp2 hrpq,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
    change 0 ≤ A - (2*r)*C + r^2*B at hn
    nlinarith
  have hdisc := discrim_le_zero hquad
  simp only [discrim] at hdisc
  have hcs : C ^ 2 ≤ A * B := by nlinarith
  have hsqrt : (Real.sqrt A * Real.sqrt B)^2 = A*B := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  exact le_of_sq_le_sq (hcs.trans_eq hsqrt.symm)
    (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))

theorem norm_product_integral_le (u f : ℝ → H) (b L : ℝ) (hL : 0 ≤ L)
    (hu : Continuous u) (hf : Continuous f) :
    (∫ x in b..b+L, ‖u x‖ * ‖f x‖) ≤ spatialL2 u b L * spatialL2 f b L :=
  spatial_integral_cauchy_schwarz (fun x => ‖u x‖) (fun x => ‖f x‖)
    hu.norm hf.norm b (b+L) (by linarith)

theorem forcingWork_pointwise_le (f u : ℝ → ℝ → H) (t x : ℝ) :
    Exp013.forcingWork f u t x ≤ 2 * (‖u t x‖ * ‖f t x‖) := by
  have h := re_inner_le_norm (𝕜 := ℂ) (u t x) ((-Complex.I) • f t x)
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

theorem forcingWork_integral_le (f u : ℝ → ℝ → H) (b L t : ℝ) (hL : 0 ≤ L)
    (hf : Continuous (f t)) (hu : Continuous (u t)) :
    (∫ x in b..b+L, Exp013.forcingWork f u t x) ≤
      2 * spatialL2 (u t) b L * spatialL2 (f t) b L := by
  have hi : Continuous (fun x => inner ℂ (u t x) ((-Complex.I) • f t x)) :=
    hu.inner (hf.const_smul (-Complex.I))
  have hw : Continuous (Exp013.forcingWork f u t) :=
    (Complex.continuous_re.comp hi).const_mul 2
  have hb : Continuous (fun x => 2 * (‖u t x‖ * ‖f t x‖)) :=
    (hu.norm.mul hf.norm).const_mul 2
  calc
    _ ≤ ∫ x in b..b+L, 2 * (‖u t x‖ * ‖f t x‖) :=
      intervalIntegral.integral_mono (by linarith)
        (hw.intervalIntegrable b (b+L)) (hb.intervalIntegrable b (b+L))
        (fun x => forcingWork_pointwise_le f u t x)
    _ = 2 * (∫ x in b..b+L, ‖u t x‖ * ‖f t x‖) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ 2 * (spatialL2 (u t) b L * spatialL2 (f t) b L) :=
      mul_le_mul_of_nonneg_left (norm_product_integral_le (u t) (f t) b L hL hu hf)
        (by norm_num)
    _ = _ := by ring

end NDEAEvolve.Exp015
