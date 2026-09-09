import Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact nonvacuity controls for the second weighted coefficient moment.
The datum has a nonzero coefficient at every signed integer. Dividing the
encoded geometric coefficient by the exact weight makes its regularity
verification independent of any asymptotic relation between encode and |m|.
It differs from the signed geometric datum in the floating-point diagnostics. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp010.Controls

def regularGeometricCoefficients (m : ℤ) : E 2 :=
  ((1 / 2 : ℂ)^Encodable.encode m / (Exp009.frequencyWeight 2 m : ℂ)) •
    Exp007.Controls.initialSpinor

theorem regular_geometric_coefficient_norm (m : ℤ) :
    ‖regularGeometricCoefficients m‖ =
      (1 / 2 : ℝ)^Encodable.encode m / Exp009.frequencyWeight 2 m := by
  simp [regularGeometricCoefficients, norm_smul, norm_div, norm_pow,
    Exp007.Controls.initialSpinor_norm,
    Real.norm_eq_abs, abs_of_nonneg (Exp009.frequencyWeight_nonneg 2 m)]

theorem regular_geometric_weighted_norm (m : ℤ) :
    Exp009.frequencyWeight 2 m * ‖regularGeometricCoefficients m‖ =
      (1 / 2 : ℝ)^Encodable.encode m := by
  rw [regular_geometric_coefficient_norm]
  have hw : Exp009.frequencyWeight 2 m ≠ 0 := by
    have := Exp009.frequencyWeight_one_le 2 m
    linarith
  exact mul_div_cancel₀ _ hw

theorem regular_geometric_regular : Regular regularGeometricCoefficients := by
  change Summable (fun m : ℤ => Exp009.frequencyWeight 2 m *
    ‖regularGeometricCoefficients m‖)
  simp only [regular_geometric_weighted_norm]
  exact summable_geometric_two_encode

theorem regular_geometric_summable_norm :
    Summable (fun m : ℤ => ‖regularGeometricCoefficients m‖) :=
  Exp009.weighted_summable_implies_absolute 2 _ regular_geometric_regular

theorem regular_geometric_coefficient_nonzero (m : ℤ) :
    regularGeometricCoefficients m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [regular_geometric_coefficient_norm]
  have hw : 0 < Exp009.frequencyWeight 2 m := by
    have := Exp009.frequencyWeight_one_le 2 m
    linarith
  positivity

theorem regular_geometric_support_all :
    Function.support regularGeometricCoefficients = Set.univ := by
  ext m
  simp [Function.mem_support, regular_geometric_coefficient_nonzero]

theorem regular_geometric_infinite_support :
    (Function.support regularGeometricCoefficients).Infinite := by
  rw [regular_geometric_support_all]
  exact Set.infinite_univ

theorem regular_geometric_tail_positive (M : ℕ) :
    0 < Exp009.tail M regularGeometricCoefficients := by
  have hm : (M : ℤ) + 1 ∉ Exp009.band M := by simp [Exp009.band]
  let j : {m : ℤ // m ∉ Exp009.band M} := ⟨(M : ℤ) + 1, hm⟩
  rw [Exp009.tail_eq_tsum_compl M regularGeometricCoefficients
    regular_geometric_summable_norm]
  have hs := regular_geometric_summable_norm.subtype (fun m => m ∉ Exp009.band M)
  have hp : 0 < ‖regularGeometricCoefficients j‖ :=
    norm_pos_iff.mpr (regular_geometric_coefficient_nonzero _)
  exact hp.trans_le (hs.le_tsum j (fun _ _ => norm_nonneg _))

theorem zero_coefficients_regular : Regular (fun _ : ℤ => (0 : E 2)) := by
  change Summable (fun m : ℤ => Exp009.frequencyWeight 2 m * ‖(0 : E 2)‖)
  simp

theorem zero_infinite_solution (t x : ℝ) :
    Exp009.infiniteSolution (fun _ : ℤ => (0 : E 2)) t x = 0 := by
  simp [Exp009.infiniteSolution, Exp008.modeSolution, Exp008.modeOrbit]

def singleCoefficients (j : ℤ) (v : E 2) (m : ℤ) : E 2 :=
  if m = j then v else 0

theorem single_coefficients_regular (j : ℤ) (v : E 2) :
    Regular (singleCoefficients j v) := by
  have he : (fun m : ℤ => Exp009.frequencyWeight 2 m * ‖singleCoefficients j v m‖) =
      (fun m : ℤ => if m = j then Exp009.frequencyWeight 2 j * ‖v‖ else 0) := by
    funext m
    by_cases hm : m = j <;> simp [singleCoefficients, hm]
  change Summable _
  rw [he]
  exact (hasSum_ite_eq j (Exp009.frequencyWeight 2 j * ‖v‖)).summable

theorem single_infinite_solution (j : ℤ) (v : E 2) (t x : ℝ) :
    Exp009.infiniteSolution (singleCoefficients j v) t x =
      Exp008.modeSolution j v t x := by
  unfold Exp009.infiniteSolution
  rw [tsum_eq_single j]
  · simp [singleCoefficients]
  · intro m hm
    simp [singleCoefficients, hm, Exp008.modeSolution, Exp008.modeOrbit]

theorem negative_frequency_derivative_sign (v : E 2) :
    deriv (Exp009.infiniteSolution (singleCoefficients (-1) v) 0) 0 =
      (-Complex.I) • v := by
  have he : Exp009.infiniteSolution (singleCoefficients (-1) v) 0 =
      Exp008.modeSolution (-1) v 0 := funext fun x => single_infinite_solution (-1) v 0 x
  rw [he, (Exp008.modeSolution_space_hasDerivAt (-1) v 0 0).deriv]
  simp

theorem positive_frequency_derivative_sign (v : E 2) :
    deriv (Exp009.infiniteSolution (singleCoefficients 1 v) 0) 0 =
      Complex.I • v := by
  have he : Exp009.infiniteSolution (singleCoefficients 1 v) 0 =
      Exp008.modeSolution 1 v 0 := funext fun x => single_infinite_solution 1 v 0 x
  rw [he, (Exp008.modeSolution_space_hasDerivAt 1 v 0 0).deriv]
  simp

theorem negative_frequency_second_derivative_sign (v : E 2) :
    deriv (deriv (Exp009.infiniteSolution (singleCoefficients (-1) v) 0)) 0 = -v := by
  have he : Exp009.infiniteSolution (singleCoefficients (-1) v) 0 =
      Exp008.modeSolution (-1) v 0 := funext fun x => single_infinite_solution (-1) v 0 x
  rw [he, Exp008.modeSolution_second_derivative]
  simp

theorem regular_geometric_classical :
    IsClassicalPeriodicSolution (Exp009.infiniteSolution regularGeometricCoefficients) :=
  infiniteSolution_classical regularGeometricCoefficients regular_geometric_regular

theorem regular_geometric_schrodinger (t x : ℝ) :
    Complex.I • deriv (fun s => Exp009.infiniteSolution regularGeometricCoefficients s x) t =
      -deriv (deriv (Exp009.infiniteSolution regularGeometricCoefficients t)) x +
        operatorOf (Exp007.Z + Exp007.X)
          (Exp009.infiniteSolution regularGeometricCoefficients t x) :=
  infiniteSolution_schrodinger regularGeometricCoefficients regular_geometric_regular t x

theorem infinite_support_classical_example :
    ∃ a : ℤ → E 2, (∀ m, a m ≠ 0) ∧ Regular a ∧
      (Function.support a).Infinite ∧ IsClassicalPeriodicSolution (Exp009.infiniteSolution a) :=
  ⟨regularGeometricCoefficients, regular_geometric_coefficient_nonzero,
    regular_geometric_regular, regular_geometric_infinite_support, regular_geometric_classical⟩

end NDEAEvolve.Exp010.Controls
