import WeightedFourier
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Regular operator-valued Fourier potentials act by a bounded convolution
on the complete second-moment coefficient space. Each shift is constructed
before taking the operator-norm convergent infinite sum. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RegularPotential (v : ℤ → H →L[ℂ] H) : Prop :=
  Summable fun j => weight j * ‖v j‖

def HermitianFourierPotential (v : ℤ → H →L[ℂ] H) : Prop :=
  ∀ j, v (-j) = star (v j)

def character (x : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))

theorem character_norm (x : ℝ) (m : ℤ) : ‖character x m‖ = 1 := by
  simp [character, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem character_continuous (m : ℤ) : Continuous (fun x => character x m) := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem character_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y => character y m) ((Complex.I * (m : ℂ)) * character x m) x := by
  simpa [character, mul_comm] using!
    (((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * (m : ℂ))).cexp).comp_ofReal

theorem character_periodic (m : ℤ) :
    Function.Periodic (fun x => character x m) (2 * Real.pi) := by
  intro x
  have he : Complex.I * (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  simp only [character, Complex.ofReal_add, mul_add, Complex.exp_add, he,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem character_add (x : ℝ) (j m : ℤ) :
    character x (j + m) = character x j * character x m := by
  simp only [character, Int.cast_add, mul_add, add_mul, Complex.exp_add]

theorem character_star (x : ℝ) (j : ℤ) :
    star (character x j) = character x (-j) := by
  simp only [character, RCLike.star_def, ← Complex.exp_conj, map_mul,
    map_intCast, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
  congr 1
  ring

theorem potential_weight_add_le (j m : ℤ) :
    weight (j + m) ≤ weight j * weight m := weight_add_le j m

theorem potential_weight_ratio_le (j m : ℤ) :
    weight m / weight (m - j) ≤ weight j := by
  apply (div_le_iff₀ (weight_pos (m - j))).mpr
  have he : j + (m - j) = m := by omega
  simpa only [he] using potential_weight_add_le j (m - j)

private def subtractEquiv (j : ℤ) : ℤ ≃ ℤ where
  toFun m := m - j
  invFun m := m + j
  left_inv m := sub_add_cancel m j
  right_inv m := add_sub_cancel_right m j

private theorem state_norm_eq (b : FourierState H) : ‖b‖ = ∑' m, ‖b m‖ := by
  exact (state_tsum_norm b).symm

private def shiftValue (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) (m : ℤ) : H :=
  ((weight m / weight (m - j) : ℝ) : ℂ) • A (b (m - j))

private theorem shiftValue_norm_le (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (m : ℤ) :
    ‖shiftValue j A b m‖ ≤ (weight j * ‖A‖) * ‖b (m - j)‖ := by
  have hr : 0 ≤ weight m / weight (m - j) :=
    div_nonneg (weight_pos m).le (weight_pos (m - j)).le
  rw [shiftValue, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  calc
    _ ≤ (weight m / weight (m - j)) * (‖A‖ * ‖b (m - j)‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) hr
    _ ≤ weight j * (‖A‖ * ‖b (m - j)‖) :=
      mul_le_mul_of_nonneg_right (potential_weight_ratio_le j m) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

private theorem shiftValue_summable_norm (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) : Summable fun m => ‖shiftValue j A b m‖ := by
  have hs : Summable fun m => ‖b (m - j)‖ :=
    (subtractEquiv j).summable_iff.mpr (state_summable_norm b)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (shiftValue_norm_le j A b) (hs.mul_left (weight j * ‖A‖))

private def shiftState (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) : FourierState H :=
  ⟨shiftValue j A b, memℓp_gen (by simpa using shiftValue_summable_norm j A b)⟩

private theorem shiftState_norm_le (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) :
    ‖shiftState j A b‖ ≤ (weight j * ‖A‖) * ‖b‖ := by
  rw [state_norm_eq]
  change (∑' m, ‖shiftValue j A b m‖) ≤ _
  have hs : Summable fun m => ‖b (m - j)‖ :=
    (subtractEquiv j).summable_iff.mpr (state_summable_norm b)
  calc
    _ ≤ ∑' m, (weight j * ‖A‖) * ‖b (m - j)‖ :=
      (shiftValue_summable_norm j A b).tsum_le_tsum (shiftValue_norm_le j A b)
        (hs.mul_left _)
    _ = (weight j * ‖A‖) * ∑' m, ‖b m‖ := by
      rw [tsum_mul_left]
      exact congrArg (fun r : ℝ => (weight j * ‖A‖) * r)
        ((subtractEquiv j).tsum_eq (fun m => ‖b m‖))
    _ = _ := by rw [← state_norm_eq]

def potentialShift (j : ℤ) (A : H →L[ℂ] H) : FourierState H →L[ℂ] FourierState H :=
  LinearMap.mkContinuous
    { toFun := shiftState j A
      map_add' := by
        intro b c
        apply lp.ext
        funext m
        simp [shiftState, shiftValue, map_add, smul_add]
      map_smul' := by
        intro z b
        apply lp.ext
        funext m
        simp [shiftState, shiftValue, map_smul, smul_smul, mul_comm] }
    (weight j * ‖A‖) (shiftState_norm_le j A)

theorem potentialShift_apply (j : ℤ) (A : H →L[ℂ] H) (b : FourierState H) (m : ℤ) :
    potentialShift j A b m = ((weight m / weight (m - j) : ℝ) : ℂ) • A (b (m - j)) := rfl

theorem potentialShift_norm_le (j : ℤ) (A : H →L[ℂ] H) :
    ‖potentialShift j A‖ ≤ weight j * ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (weight_pos j).le (norm_nonneg A))
  exact shiftState_norm_le j A

theorem coefficient_potentialShift (j : ℤ) (A : H →L[ℂ] H)
    (b : FourierState H) (m : ℤ) :
    coefficient (potentialShift j A b) m = A (coefficient b (m - j)) := by
  simp only [coefficient, potentialShift_apply, map_smul, smul_smul]
  congr 1
  have hm : (weight m : ℂ) ≠ 0 := by exact_mod_cast (weight_pos m).ne'
  have hj : (weight (m - j) : ℂ) ≠ 0 := by exact_mod_cast (weight_pos (m - j)).ne'
  push_cast
  field_simp [hm, hj]

def potentialConvolution (v : ℤ → H →L[ℂ] H) : FourierState H →L[ℂ] FourierState H :=
  ∑' j, potentialShift j (v j)

theorem potentialShift_summable_norm (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => ‖potentialShift j (v j)‖ := by
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg (potentialShift j (v j)))
    (fun j => potentialShift_norm_le j (v j)) hv

theorem potentialShift_summable (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => potentialShift j (v j) := by
  exact hv.of_norm_bounded (fun j => potentialShift_norm_le j (v j))

theorem potentialConvolution_norm_le (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    ‖potentialConvolution v‖ ≤ ∑' j, weight j * ‖v j‖ := by
  change ‖∑' j, potentialShift j (v j)‖ ≤ _
  exact (norm_tsum_le_tsum_norm (f := fun j => potentialShift j (v j))
    (potentialShift_summable_norm v hv)).trans
    ((potentialShift_summable_norm v hv).tsum_le_tsum
      (fun j => potentialShift_norm_le j (v j)) hv)

theorem potentialConvolution_apply (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b : FourierState H) :
    potentialConvolution v b = ∑' j, potentialShift j (v j) b := by
  exact (ContinuousLinearMap.apply ℂ (FourierState H) b).map_tsum (potentialShift_summable v hv)

theorem coefficient_potentialConvolution (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b : FourierState H) (m : ℤ) :
    coefficient (potentialConvolution v b) m = ∑' j, v j (coefficient b (m - j)) := by
  rw [potentialConvolution_apply v hv]
  have hs : Summable (fun j => potentialShift j (v j) b) :=
    (potentialShift_summable v hv).mapL (ContinuousLinearMap.apply ℂ (FourierState H) b)
  change coefficientCLM m (∑' j, potentialShift j (v j) b) = _
  exact ((coefficientCLM m).map_tsum hs).trans
    (tsum_congr fun j => coefficient_potentialShift j (v j) b m)

def operatorPotential (v : ℤ → H →L[ℂ] H) (x : ℝ) : H →L[ℂ] H :=
  ∑' j, character x j • v j

theorem regularPotential_absolute (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v) :
    Summable fun j => ‖v j‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hv
  intro j
  exact le_mul_of_one_le_left (norm_nonneg _) (weight_one_le j)

theorem operatorPotential_summable_norm (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (x : ℝ) :
    Summable fun j => ‖character x j • v j‖ := by
  simpa only [norm_smul, character_norm, one_mul] using regularPotential_absolute v hv

theorem operatorPotential_apply (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (x : ℝ) (y : H) :
    operatorPotential v x y = ∑' j, character x j • v j y := by
  exact (ContinuousLinearMap.apply ℂ H y).map_tsum
    (operatorPotential_summable_norm v hv x).of_norm

theorem operatorPotential_norm_le (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (x : ℝ) : ‖operatorPotential v x‖ ≤ ∑' j, ‖v j‖ := by
  unfold operatorPotential
  simpa only [norm_smul, character_norm, one_mul] using
    norm_tsum_le_tsum_norm (operatorPotential_summable_norm v hv x)

theorem operatorPotential_periodic (v : ℤ → H →L[ℂ] H) :
    Function.Periodic (operatorPotential v) (2 * Real.pi) := by
  intro x
  unfold operatorPotential
  apply tsum_congr
  intro j
  exact congrArg (fun z : ℂ => z • v j) (character_periodic j x)

theorem operatorPotential_continuous (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) : Continuous (operatorPotential v) := by
  exact continuous_tsum (fun j => (character_continuous j).smul continuous_const)
    (regularPotential_absolute v hv) (fun j x => by simp [norm_smul, character_norm])

theorem operatorPotential_selfAdjoint (v : ℤ → H →L[ℂ] H)
    (hv : HermitianFourierPotential v) (x : ℝ) : IsSelfAdjoint (operatorPotential v x) := by
  change star (operatorPotential v x) = operatorPotential v x
  rw [operatorPotential, tsum_star]
  calc
    (∑' j, star (character x j • v j)) = ∑' j, character x (-j) • v (-j) := by
      apply tsum_congr
      intro j
      rw [star_smul, character_star, ← hv j]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun j => character x j • v j)

end NDEAEvolve.Exp014
