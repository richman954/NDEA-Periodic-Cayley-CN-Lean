import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Concrete periodic split-Schrodinger residual. No residual bound is assumed.
The physical mode is nonconstant and both split generators act nontrivially.
This is a commuting, single-mode milestone; it is not a general PDE closure. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp006

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by simp [phase]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_formula (x : ℝ) :
    phase x = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  exact Complex.exp_ofReal_mul_I x

def mode (t x : ℝ) : ℂ := phase (x - 2*t)

 theorem phase_periodic : Function.Periodic phase (2*Real.pi) := by
  intro x
  simpa [phase, Complex.ofReal_add, Complex.ofReal_mul] using
    Complex.exp_mul_I_periodic (x : ℂ)

 theorem mode_periodic (t : ℝ) : Function.Periodic (mode t) (2*Real.pi) := by
  intro x
  change phase ((x+2*Real.pi)-2*t) = phase (x-2*t)
  rw [show (x+2*Real.pi)-2*t = (x-2*t)+2*Real.pi by ring]
  exact phase_periodic (x-2*t)

 theorem phase_hasDerivAt (x : ℝ) : HasDerivAt phase (phase x * Complex.I) x := by
  simpa [phase] using! (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).cexp).comp_ofReal

 theorem mode_space_hasDerivAt (t x : ℝ) :
    HasDerivAt (mode t) (mode t x * Complex.I) x := by
  change HasDerivAt (fun y => phase (y-2*t)) (phase (x-2*t)*Complex.I) x
  simpa [mode, Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using! (phase_hasDerivAt (x-2*t)).scomp x ((hasDerivAt_id x).sub_const (2*t))

 theorem mode_time_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun s => mode s x) (mode t x * Complex.I * (-2)) t := by
  simpa [mode, Function.comp_def, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using! (phase_hasDerivAt (x-2*t)).scomp t
    ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul 2))

 theorem mode_second_derivative (t x : ℝ) : deriv (deriv (mode t)) x = - mode t x := by
  have hd : deriv (mode t) = fun y => mode t y * Complex.I :=
    funext fun y => (mode_space_hasDerivAt t y).deriv
  rw [hd, ((mode_space_hasDerivAt t x).mul_const Complex.I).deriv]
  simp [mul_assoc]

 /-- The displayed PDE is checked with genuine real derivatives. -/
 theorem mode_solves_split_schrodinger (t x : ℝ) :
    Complex.I * deriv (fun s => mode s x) t = -2 * deriv (deriv (mode t)) x := by
  rw [(mode_time_hasDerivAt t x).deriv, mode_second_derivative]
  calc
    _ = (Complex.I*Complex.I) * (-2) * mode t x := by ring
    _ = _ := by simp

 theorem mode_nonzero (t x : ℝ) : mode t x ≠ 0 := by
  exact Complex.exp_ne_zero _

 theorem mode_nonconstant (t : ℝ) : ∃ x y, mode t x ≠ mode t y := by
  refine ⟨2*t, 2*t+Real.pi, ?_⟩
  simp only [mode, phase, show 2*t-2*t=0 by ring,
    show 2*t+Real.pi-2*t=Real.pi by ring]
  norm_num [Complex.exp_pi_mul_I]

def spatialSymbol (h : ℝ) : ℝ := (2 - 2 * Real.cos h) / h^2

/-- The actual centered negative second difference on an unwrapped sample.
For the periodic mode, unwrapped and periodically wrapped samples agree. -/
def centeredStencil (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 * f x - f (x+h) - f (x-h)) / (h : ℂ)^2

theorem phase_centeredStencil (h x : ℝ) :
    centeredStencil h phase x = (spatialSymbol h : ℂ) * phase x := by
  have hadd : phase (x+h) = phase x * phase h := phase_add x h
  have hsub : phase (x-h) = phase x * phase (-h) := by
    simpa [sub_eq_add_neg] using phase_add x (-h)
  have hsum : phase h + phase (-h) = (2 * Real.cos h : ℝ) := by
    rw [phase_formula, phase_formula]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  unfold centeredStencil spatialSymbol
  rw [hadd, hsub]
  push_cast
  calc
    _ = (2 - (phase h + phase (-h))) / (h : ℂ)^2 * phase x := by ring
    _ = _ := by rw [hsum]; push_cast; ring

/-- A concrete mesh-uniform spatial estimate, from the library cosine Taylor
remainder. The 1/8 constant is deliberately rounded upward. -/
theorem spatialSymbol_consistency (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1) :
    |spatialSymbol h - 1| ≤ h^2 / 8 := by
  have hc := Real.cos_bound (x := h) (by rwa [abs_of_pos hh])
  rw [abs_of_pos hh] at hc
  have hid : spatialSymbol h - 1 = -2 * (Real.cos h - (1 - h^2/2)) / h^2 := by
    unfold spatialSymbol
    field_simp
    <;> ring
  rw [hid, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hh)]
  norm_num
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  nlinarith [sq_nonneg (h^2)]

/-- On every nonzero mesh the first Fourier symbol has genuine spatial error. -/
theorem spatialSymbol_strictly_below_continuum (h : ℝ) (hh : h ≠ 0) :
    spatialSymbol h < 1 := by
  unfold spatialSymbol
  apply (div_lt_one (sq_pos_of_ne_zero hh)).2
  have hc := Real.one_sub_sq_div_two_lt_cos hh
  nlinarith

theorem sin_linear_remainder (a : ℝ) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    |Real.sin a - a| ≤ a^3/4 := by
  have hs := Real.sin_bound (x := a) (by rwa [abs_of_nonneg ha])
  rw [abs_of_nonneg ha] at hs
  have hp : a^4 ≤ a^3 := by
    calc
      a^4 = a^3*a := by ring
      _ ≤ a^3*1 := mul_le_mul_of_nonneg_left hasmall (pow_nonneg ha _)
      _ = a^3 := mul_one _
  have htri : |Real.sin a - a| ≤ |Real.sin a - (a-a^3/6)| + a^3/6 := by
    calc
      _ = |(Real.sin a - (a-a^3/6)) + (-(a^3/6))| := by congr 1; ring
      _ ≤ |Real.sin a - (a-a^3/6)| + |-(a^3/6)| := abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_of_nonneg (show 0 ≤ a^3/6 by positivity)]
  nlinarith [pow_nonneg ha 3]

theorem cos_linear_remainder (a : ℝ) : |Real.cos a - 1| ≤ a^2/2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one a))]
  have h := Real.one_sub_sq_div_two_le_cos (x := a)
  linarith

theorem midpoint_temporal_remainder (a : ℝ) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    |a * Real.cos a - Real.sin a| ≤ a^3 := by
  calc
    _ = |a * (Real.cos a - 1) - (Real.sin a - a)| := by congr 1; ring
    _ ≤ |a * (Real.cos a - 1)| + |Real.sin a - a| := abs_sub _ _
    _ = a * |Real.cos a - 1| + |Real.sin a - a| := by
      rw [abs_mul, abs_of_nonneg ha]
    _ ≤ a * (a^2/2) + a^3/4 :=
      add_le_add (mul_le_mul_of_nonneg_left (cos_linear_remainder a) ha)
        (sin_linear_remainder a ha hasmall)
    _ ≤ a^3 := by nlinarith [pow_nonneg ha 3]

/-- Unscaled denominator-times-target minus numerator-times-source. -/
def scalarFactorResidual (h a x : ℝ) : ℂ :=
  (1 + Complex.I * (a : ℂ) * (spatialSymbol h : ℂ)) * phase (x-2*a) -
  (1 - Complex.I * (a : ℂ) * (spatialSymbol h : ℂ)) * phase x

theorem scalarFactorResidual_midpoint (h a x : ℝ) :
    scalarFactorResidual h a x = phase (x-a) * (2 * Complex.I) *
      ((a * spatialSymbol h * Real.cos a - Real.sin a : ℝ) : ℂ) := by
  have hminus : phase (x-2*a) = phase (x-a) * phase (-a) := by
    rw [← phase_add]; congr 1; ring
  have hplus : phase x = phase (x-a) * phase a := by
    rw [← phase_add]; congr 1; ring
  unfold scalarFactorResidual
  rw [hminus, hplus, phase_formula (-a), phase_formula a]
  simp only [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem scalarFactorResidual_bound (h a x : ℝ)
    (hh : 0 < h) (hhsmall : h ≤ 1) (ha : 0 ≤ a) (hasmall : a ≤ 1) :
    ‖scalarFactorResidual h a x‖ ≤ 2*a^3 + a*h^2/4 := by
  have hs := spatialSymbol_consistency h hh hhsmall
  have ht := midpoint_temporal_remainder a ha hasmall
  have hmid : |a * spatialSymbol h * Real.cos a - Real.sin a| ≤
      a * (h^2/8) + a^3 := by
    calc
      _ = |a * (spatialSymbol h - 1) * Real.cos a +
        (a * Real.cos a - Real.sin a)| := by congr 1; ring
      _ ≤ |a * (spatialSymbol h - 1) * Real.cos a| +
        |a * Real.cos a - Real.sin a| := abs_add_le _ _
      _ = a * |spatialSymbol h - 1| * |Real.cos a| +
        |a * Real.cos a - Real.sin a| := by rw [abs_mul, abs_mul, abs_of_nonneg ha]
      _ ≤ a * (h^2/8) * 1 + a^3 := by
        apply add_le_add _ ht
        exact mul_le_mul (mul_le_mul_of_nonneg_left hs ha) (Real.abs_cos_le_one a)
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [scalarFactorResidual_midpoint, norm_mul, norm_mul, phase_norm]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  norm_num
  nlinarith

#print axioms phase_centeredStencil
#print axioms spatialSymbol_consistency
#print axioms scalarFactorResidual_bound
end NDEAEvolve.Exp006
