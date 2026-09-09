import WeightedTail

noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
namespace NDEAEvolve.Exp010.Probe

def modeTime (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (-Complex.I) • operatorOf (modeGenerator m) (modeSolution m v t x)
def modeSpace (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (Complex.I * (m : ℂ)) • modeSolution m v t x
def modeSecond (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  -((m : ℂ)^2) • modeSolution m v t x

theorem mode_time_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (fun s => modeSolution m v s x) (modeTime m v t x) t := by
  simpa [modeTime, modeSolution, map_smul, smul_smul, mul_comm] using
    modeSolution_time_hasDerivAt m v t x

theorem mode_space_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSolution m v t) (modeSpace m v t x) x := by
  simpa [modeSpace, modeSolution, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    modeSolution_space_hasDerivAt m v t x

theorem mode_second_hasDerivAt (m : ℤ) (v : E 2) (t x : ℝ) :
    HasDerivAt (modeSpace m v t) (modeSecond m v t x) x := by
  have h : modeSpace m v t = deriv (modeSolution m v t) :=
    funext fun y => (mode_space_hasDerivAt m v t y).deriv.symm
  rw [h]
  exact modeSolution_second_hasDerivAt m v t x

theorem mode_schrodinger (m : ℤ) (v : E 2) (t x : ℝ) :
    Complex.I • modeTime m v t x =
      -modeSecond m v t x + operatorOf (Exp007.Z + Exp007.X) (modeSolution m v t x) := by
  rw [← (mode_time_hasDerivAt m v t x).deriv]
  simpa [modeSecond, modeSolution_second_derivative] using modeSolution_schrodinger m v t x

theorem modeSolution_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSolution m v p.1 p.2) := by
  have ht : Continuous (fun t : ℝ => modeOrbit m t v) :=
    continuous_iff_continuousAt.mpr fun t => (modeOrbit_hasDerivAt m v t).continuousAt
  have hx : Continuous (fun x : ℝ => Exp006.phase ((m : ℝ) * x)) :=
    continuous_iff_continuousAt.mpr fun x => (phaseMode_hasDerivAt m x).continuousAt
  exact (hx.comp continuous_snd).smul (ht.comp continuous_fst)

theorem modeTime_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeTime m v p.1 p.2) := by
  exact ((operatorOf (modeGenerator m)).continuous.comp
    (modeSolution_continuous m v)).const_smul (-Complex.I)

end NDEAEvolve.Exp010.Probe
