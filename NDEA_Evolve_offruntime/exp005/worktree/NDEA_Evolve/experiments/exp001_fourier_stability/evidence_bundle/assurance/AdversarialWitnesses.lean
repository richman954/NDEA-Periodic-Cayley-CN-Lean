import NDEAEvolve.Experiments.Exp001.FourierStability

open NDEAEvolve.Exp001

noncomputable section

example : ‖cayleyFactor 0‖ = 1 := cayleyFactor_norm_one 0

example :
    cayleyDenominator 1 * cayleyFactor 1 = cayleyNumerator 1 :=
  cayleyFactor_satisfies_update 1

def generalizedCayleyWitness (a : ℂ) : ℂ :=
  ((1 : ℂ) - Complex.I * a) / ((1 : ℂ) + Complex.I * a)

example : generalizedCayleyWitness (Complex.I / 2) = 3 := by
  have hnum :
      (1 : ℂ) - Complex.I * (Complex.I / 2) = 3 / 2 := by
    calc
      (1 : ℂ) - Complex.I * (Complex.I / 2) =
          1 - (Complex.I * Complex.I) / 2 := by ring
      _ = 1 - (-1) / 2 := by rw [Complex.I_mul_I]
      _ = 3 / 2 := by norm_num
  have hden :
      (1 : ℂ) + Complex.I * (Complex.I / 2) = 1 / 2 := by
    calc
      (1 : ℂ) + Complex.I * (Complex.I / 2) =
          1 + (Complex.I * Complex.I) / 2 := by ring
      _ = 1 + (-1) / 2 := by rw [Complex.I_mul_I]
      _ = 1 / 2 := by norm_num
  rw [generalizedCayleyWitness, hnum, hden]
  norm_num

example : realStencilSymbol Real.pi = 4 := by
  norm_num [realStencilSymbol]
