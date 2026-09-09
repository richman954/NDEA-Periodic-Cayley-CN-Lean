import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The centered quadratic time reconstruction and its exact operator residual.
The endpoint defect is retained without a residual-smallness hypothesis.
These are state-space identities; no spatial or PDE regularity is asserted. -/
noncomputable section

namespace NDEAEvolve.Exp016

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def quadraticOffset (t₀ k t : ℝ) : ℝ := t - (t₀ + k / 2)

def quadraticCorrection (t₀ k t : ℝ) : ℂ :=
  (Complex.I / 2) * ((quadraticOffset t₀ k t : ℂ) ^ 2 - (k : ℂ) ^ 2 / 4)

def quadraticTime (H : E →L[ℂ] E) (m v : E) (t₀ k t : ℝ) : E :=
  m + (quadraticOffset t₀ k t : ℂ) • v - quadraticCorrection t₀ k t • H v

def quadraticMean (u₀ u₁ : E) : E := (1 / 2 : ℂ) • (u₀ + u₁)

def quadraticVelocity (u₀ u₁ : E) (k : ℝ) : E :=
  (k : ℂ)⁻¹ • (u₁ - u₀)

def quadraticSlab (H : E →L[ℂ] E) (u₀ u₁ : E) (t₀ k t : ℝ) : E :=
  quadraticTime H (quadraticMean u₀ u₁) (quadraticVelocity u₀ u₁ k) t₀ k t

private theorem quadratic_offset_complex_hasDerivAt (t₀ k t : ℝ) :
    HasDerivAt (fun s : ℝ => (quadraticOffset t₀ k s : ℂ)) (1 : ℂ) t := by
  simpa only [quadraticOffset, Complex.ofReal_one, id_eq] using!
    ((hasDerivAt_id t).sub_const (t₀ + k / 2)).ofReal_comp

theorem quadraticCorrection_hasDerivAt (t₀ k t : ℝ) :
    HasDerivAt (quadraticCorrection t₀ k)
      (Complex.I * (quadraticOffset t₀ k t : ℂ)) t := by
  have h := (((quadratic_offset_complex_hasDerivAt t₀ k t).pow 2).sub_const
    ((k : ℂ) ^ 2 / 4)).const_mul (Complex.I / 2)
  have hv : (Complex.I / 2) *
      ((2 : ℂ) * (quadraticOffset t₀ k t : ℂ) ^ (2 - 1) * 1) =
      Complex.I * (quadraticOffset t₀ k t : ℂ) := by ring
  simpa only [quadraticCorrection, Nat.cast_ofNat, hv, Pi.pow_apply] using! h

theorem quadraticTime_hasDerivAt (H : E →L[ℂ] E) (m v : E) (t₀ k t : ℝ) :
    HasDerivAt (quadraticTime H m v t₀ k)
      (v - (Complex.I * (quadraticOffset t₀ k t : ℂ)) • H v) t := by
  have hlinear := (quadratic_offset_complex_hasDerivAt t₀ k t).smul_const v
  have hcorrection := (quadraticCorrection_hasDerivAt t₀ k t).smul_const (H v)
  simpa only [quadraticTime, one_smul, Pi.sub_apply] using!
    (hlinear.const_add m).sub hcorrection

theorem quadraticTime_derivative (H : E →L[ℂ] E) (m v : E) (t₀ k t : ℝ) :
    deriv (quadraticTime H m v t₀ k) t =
      v - (Complex.I * (quadraticOffset t₀ k t : ℂ)) • H v :=
  (quadraticTime_hasDerivAt H m v t₀ k t).deriv

theorem quadraticTime_left (H : E →L[ℂ] E) (m v : E) (t₀ k : ℝ) :
    quadraticTime H m v t₀ k t₀ = m - ((k : ℂ) / 2) • v := by
  have ho : (quadraticOffset t₀ k t₀ : ℂ) = -(k : ℂ) / 2 := by
    simp only [quadraticOffset, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hc : quadraticCorrection t₀ k t₀ = 0 := by
    rw [quadraticCorrection, ho]
    ring
  simp only [quadraticTime, ho, hc, zero_smul, neg_div, neg_smul,
    sub_eq_add_neg, neg_zero, add_zero]

theorem quadraticTime_right (H : E →L[ℂ] E) (m v : E) (t₀ k : ℝ) :
    quadraticTime H m v t₀ k (t₀ + k) = m + ((k : ℂ) / 2) • v := by
  have ho : (quadraticOffset t₀ k (t₀ + k) : ℂ) = (k : ℂ) / 2 := by
    simp only [quadraticOffset, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hc : quadraticCorrection t₀ k (t₀ + k) = 0 := by
    rw [quadraticCorrection, ho]
    ring
  simp only [quadraticTime, ho, hc, zero_smul, sub_zero]

theorem quadraticSlab_left (H : E →L[ℂ] E) (u₀ u₁ : E)
    (t₀ k : ℝ) (hk : k ≠ 0) : quadraticSlab H u₀ u₁ t₀ k t₀ = u₀ := by
  have hkC : (k : ℂ) ≠ 0 := by
    intro h
    apply hk
    exact Complex.ofReal_eq_zero.mp h
  have hcancel : ((k : ℂ) / 2) * (k : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    field_simp
  rw [quadraticSlab, quadraticTime_left, quadraticMean, quadraticVelocity,
    smul_smul, hcancel]
  module

theorem quadraticSlab_right (H : E →L[ℂ] E) (u₀ u₁ : E)
    (t₀ k : ℝ) (hk : k ≠ 0) : quadraticSlab H u₀ u₁ t₀ k (t₀ + k) = u₁ := by
  have hkC : (k : ℂ) ≠ 0 := by
    intro h
    apply hk
    exact Complex.ofReal_eq_zero.mp h
  have hcancel : ((k : ℂ) / 2) * (k : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    field_simp
  rw [quadraticSlab, quadraticTime_right, quadraticMean, quadraticVelocity,
    smul_smul, hcancel]
  module

/-- The actual derivative leaves the full endpoint defect `i*v-H*m` explicit. -/
theorem quadraticTime_gridResidual (H : E →L[ℂ] E) (m v : E) (t₀ k t : ℝ) :
    Complex.I • deriv (quadraticTime H m v t₀ k) t - H (quadraticTime H m v t₀ k t) =
      (Complex.I • v - H m) + quadraticCorrection t₀ k t • H (H v) := by
  rw [quadraticTime_derivative]
  simp only [quadraticTime, map_add, map_sub, map_smul]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem quadraticSlab_hasDerivAt (H : E →L[ℂ] E) (u₀ u₁ : E) (t₀ k t : ℝ) :
    HasDerivAt (quadraticSlab H u₀ u₁ t₀ k)
      (quadraticVelocity u₀ u₁ k - (Complex.I * (quadraticOffset t₀ k t : ℂ)) •
        H (quadraticVelocity u₀ u₁ k)) t :=
  quadraticTime_hasDerivAt H (quadraticMean u₀ u₁) (quadraticVelocity u₀ u₁ k) t₀ k t

theorem quadraticSlab_gridResidual (H : E →L[ℂ] E) (u₀ u₁ : E) (t₀ k t : ℝ) :
    Complex.I • deriv (quadraticSlab H u₀ u₁ t₀ k) t - H (quadraticSlab H u₀ u₁ t₀ k t) =
      (Complex.I • quadraticVelocity u₀ u₁ k - H (quadraticMean u₀ u₁)) +
        quadraticCorrection t₀ k t • H (H (quadraticVelocity u₀ u₁ k)) :=
  quadraticTime_gridResidual H (quadraticMean u₀ u₁) (quadraticVelocity u₀ u₁ k) t₀ k t

end NDEAEvolve.Exp016
