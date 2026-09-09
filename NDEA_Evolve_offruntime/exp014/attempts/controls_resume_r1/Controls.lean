import ClassicalExistence
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact nonvacuity checks for the all-mode existence theorem. A potential
with two nonzero Fourier coefficients is spatially nonconstant. Initial data
include a signed single mode and a regular family nonzero at every integer.
These controls instantiate the constructed PDE solution, not a truncation. -/
noncomputable section
open scoped BigOperators
namespace NDEAEvolve.Exp014.Controls

def singleData (j m : ℤ) : ℂ := if m = j then 1 else 0

theorem singleData_regular (j : ℤ) :
    Summable (fun m : ℤ => weight m * ‖singleData j m‖) := by
  have he : (fun m : ℤ => weight m * ‖singleData j m‖) =
      (fun m : ℤ => if m = j then weight j else 0) := by
    funext m
    by_cases hm : m = j <;> simp [singleData, hm]
  rw [he]
  exact (hasSum_ite_eq j (weight j)).summable

theorem singleData_synthesis (j : ℤ) (x : ℝ) :
    (∑' m : ℤ, character x m • singleData j m) = character x j := by
  rw [tsum_eq_single j]
  · simp [singleData]
  · intro m hm
    simp [singleData, hm]

theorem negative_frequency_free_derivative :
    HasDerivAt (fun t : ℝ => phase t (-1)) (-Complex.I) 0 := by
  simpa [phase_zero] using phase_hasDerivAt 0 (-1)

def pairPotential (m : ℤ) : ℂ →L[ℂ] ℂ :=
  if m = 1 ∨ m = -1 then ContinuousLinearMap.id ℂ ℂ else 0

private theorem pairPotential_offsupport (m : ℤ)
    (hm : m ∉ ({1, -1} : Finset ℤ)) : pairPotential m = 0 := by
  have hn : m ≠ 1 ∧ m ≠ -1 := by simpa using hm
  simp [pairPotential, hn.1, hn.2]

theorem pairPotential_regular : RegularPotential pairPotential := by
  apply (hasSum_sum_of_ne_finset_zero (s := ({1, -1} : Finset ℤ))
    (f := fun m : ℤ => weight m * ‖pairPotential m‖) ?_).summable
  intro m hm
  simp only [pairPotential_offsupport m hm, norm_zero, mul_zero]

theorem pairPotential_hermitian : HermitianFourierPotential pairPotential := by
  intro m
  have hi : star (ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ := by
    change star (1 : ℂ →L[ℂ] ℂ) = 1
    simp
  have he : (-m = 1 ∨ -m = -1) ↔ (m = 1 ∨ m = -1) := by omega
  by_cases hm : m = 1 ∨ m = -1
  · simp only [pairPotential, if_pos hm, if_pos (he.mpr hm), hi]
  · simp only [pairPotential, if_neg hm, if_neg (not_congr he |>.mpr hm), star_zero]

theorem pairPotential_apply (x : ℝ) (z : ℂ) :
    operatorPotential pairPotential x z = character x 1 * z + character x (-1) * z := by
  rw [operatorPotential_apply pairPotential pairPotential_regular,
    tsum_eq_sum (s := ({1, -1} : Finset ℤ))]
  · norm_num [pairPotential, smul_eq_mul]
  · intro m hm
    simp only [pairPotential_offsupport m hm, ContinuousLinearMap.zero_apply, smul_zero]

theorem pairPotential_at_zero : operatorPotential pairPotential 0 1 = 2 := by
  rw [pairPotential_apply]
  norm_num [character]

theorem pairPotential_at_pi : operatorPotential pairPotential Real.pi 1 = -2 := by
  rw [pairPotential_apply]
  have hp : character Real.pi 1 = -1 := by
    simpa [character, mul_comm] using Complex.exp_pi_mul_I
  have hn : character Real.pi (-1) = -1 := by
    simpa [character, mul_comm] using Complex.exp_neg_pi_mul_I
  rw [hp, hn]
  norm_num

theorem pairPotential_nonconstant :
    operatorPotential pairPotential 0 ≠ operatorPotential pairPotential Real.pi := by
  intro h
  have he := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  rw [pairPotential_at_zero, pairPotential_at_pi] at he
  norm_num at he

theorem pairPotential_selfAdjoint (x : ℝ) :
    IsSelfAdjoint (operatorPotential pairPotential x) :=
  operatorPotential_selfAdjoint pairPotential pairPotential_hermitian x

theorem zeroPotential_regular : RegularPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) := by
  simp [RegularPotential]

theorem zeroPotential_hermitian :
    HermitianFourierPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) := by
  intro m
  simp

theorem zeroPotential_field (x : ℝ) :
    operatorPotential (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ)) x = 0 := by
  simp [operatorPotential]

def infiniteData (m : ℤ) : ℂ :=
  (1 / 2 : ℂ)^Encodable.encode m / (weight m : ℂ)

theorem infiniteData_norm (m : ℤ) :
    ‖infiniteData m‖ = (1 / 2 : ℝ)^Encodable.encode m / weight m := by
  simp [infiniteData, norm_div, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (weight_pos m).le]

theorem infiniteData_weighted_norm (m : ℤ) :
    weight m * ‖infiniteData m‖ = (1 / 2 : ℝ)^Encodable.encode m := by
  rw [infiniteData_norm]
  exact mul_div_cancel₀ _ (weight_pos m).ne'

theorem infiniteData_regular :
    Summable (fun m : ℤ => weight m * ‖infiniteData m‖) := by
  simp only [infiniteData_weighted_norm]
  exact summable_geometric_two_encode

theorem infiniteData_nonzero (m : ℤ) : infiniteData m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [infiniteData_norm]
  have hw := weight_pos m
  positivity

theorem infiniteData_support_all : Function.support infiniteData = Set.univ := by
  ext m
  simp [Function.mem_support, infiniteData_nonzero]

theorem infiniteData_infinite_support : (Function.support infiniteData).Infinite := by
  rw [infiniteData_support_all]
  exact Set.infinite_univ

theorem variablePotential_singleMode_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi)
        (fun _ x => operatorPotential pairPotential x) 0 u ∧
      ∀ x, u 0 x = character x (-1) := by
  simpa only [singleData_synthesis] using
    global_classical_exists_unique pairPotential pairPotential_regular pairPotential_hermitian
      (singleData (-1)) (singleData_regular (-1))

theorem zeroPotential_infiniteData_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi) 0 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • infiniteData m := by
  simpa only [zeroPotential_field] using
    global_classical_exists_unique (fun _ : ℤ => (0 : ℂ →L[ℂ] ℂ))
      zeroPotential_regular zeroPotential_hermitian infiniteData infiniteData_regular

theorem variablePotential_infiniteData_exists_unique :
    ∃! u : ℝ → ℝ → ℂ,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi)
        (fun _ x => operatorPotential pairPotential x) 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • infiniteData m :=
  global_classical_exists_unique pairPotential pairPotential_regular pairPotential_hermitian
    infiniteData infiniteData_regular

end NDEAEvolve.Exp014.Controls
