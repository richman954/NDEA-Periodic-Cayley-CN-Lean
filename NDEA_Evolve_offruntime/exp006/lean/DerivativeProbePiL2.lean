import DerivativeProbe
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace NDEAEvolve.Exp006.DerivativeProbePiL2

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

theorem phase_hasDerivAt (x : ℝ) : HasDerivAt phase (phase x * Complex.I) x := by
  simpa [phase] using!
    (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).cexp).comp_ofReal

theorem phase_hasDerivAt_real (x : ℝ) : HasDerivAt phase (phase x * Complex.I) x := by
  simpa [phase] using!
    (((hasDerivAt_id x).ofReal_comp).mul_const Complex.I).cexp

#print axioms phase_hasDerivAt
#print axioms phase_hasDerivAt_real

end NDEAEvolve.Exp006.DerivativeProbePiL2
