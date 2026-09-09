import SuperpositionClosure
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
namespace NDEAEvolve.Exp009.Controls

def geometricCoefficients (m : ℤ) : E 2 :=
  ((1/2 : ℂ)^Encodable.encode m) • Exp007.Controls.initialSpinor

theorem geometric_coefficient_norm (m : ℤ) :
    ‖geometricCoefficients m‖ = (1/2 : ℝ)^Encodable.encode m := by
  simp [geometricCoefficients, norm_smul, norm_pow, Exp007.Controls.initialSpinor_norm]

theorem geometric_summable_norm : Summable (fun m : ℤ => ‖geometricCoefficients m‖) := by
  simp only [geometric_coefficient_norm]
  exact summable_geometric_two_encode

theorem geometric_coefficient_nonzero (m : ℤ) : geometricCoefficients m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [geometric_coefficient_norm]
  positivity

theorem geometric_support_all : Function.support geometricCoefficients = Set.univ := by
  ext m
  simp [Function.mem_support, geometric_coefficient_nonzero]

theorem geometric_infinite_support : (Function.support geometricCoefficients).Infinite := by
  rw [geometric_support_all]
  exact Set.infinite_univ

#check Summable.le_tsum
#check Summable.le_tsum'
#print axioms geometric_summable_norm
#print axioms geometric_infinite_support
end NDEAEvolve.Exp009.Controls
