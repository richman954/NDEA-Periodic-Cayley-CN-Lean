import Regularity
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Actual derivatives of the infinite Fourier solution. The second weighted
coefficient moment supplies summable bounds uniform in time and position, so
the three exchanges of derivative and infinite sum are proved here. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
namespace NDEAEvolve.Exp010

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

theorem infiniteSolution_time_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (fun s => Exp009.infiniteSolution a s x)
      (∑' m, modeTime m (a m) t x) t := by
  exact hasDerivAt_tsum (regular_time_majorant a ha)
    (fun m s => mode_time_hasDerivAt m (a m) s x)
    (fun m s => modeTime_norm_le m (a m) s x)
    (Exp009.modeSolution_summable a (regular_absolute a ha) 0 x) t

theorem infiniteSolution_space_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (Exp009.infiniteSolution a t)
      (∑' m, modeSpace m (a m) t x) x := by
  exact hasDerivAt_tsum ha
    (fun m y => mode_space_hasDerivAt m (a m) t y)
    (fun m y => modeSpace_norm_le m (a m) t y)
    (Exp009.modeSolution_summable a (regular_absolute a ha) t 0) x

theorem infiniteSolution_time_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (fun s => Exp009.infiniteSolution a s x) t = ∑' m, modeTime m (a m) t x :=
  (infiniteSolution_time_hasDerivAt a ha t x).deriv

theorem infiniteSolution_space_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (Exp009.infiniteSolution a t) x = ∑' m, modeSpace m (a m) t x :=
  (infiniteSolution_space_hasDerivAt a ha t x).deriv

theorem infiniteSolution_second_hasDerivAt (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    HasDerivAt (deriv (Exp009.infiniteSolution a t))
      (∑' m, modeSecond m (a m) t x) x := by
  have he : deriv (Exp009.infiniteSolution a t) =
      fun y => ∑' m, modeSpace m (a m) t y :=
    funext (infiniteSolution_space_derivative a ha t)
  rw [he]
  exact hasDerivAt_tsum ha
    (fun m y => mode_second_hasDerivAt m (a m) t y)
    (fun m y => modeSecond_norm_le m (a m) t y)
    (regular_space_summable a ha t 0) x

theorem infiniteSolution_second_derivative (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    deriv (deriv (Exp009.infiniteSolution a t)) x = ∑' m, modeSecond m (a m) t x :=
  (infiniteSolution_second_hasDerivAt a ha t x).deriv

/-- The infinite series solves the spinor Schrödinger equation in actual real
time and space derivatives, with the same noncommuting split potential as the
finite-band predecessor. -/
theorem infiniteSolution_schrodinger (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Complex.I • deriv (fun s => Exp009.infiniteSolution a s x) t =
      -deriv (deriv (Exp009.infiniteSolution a t)) x +
        operatorOf (Exp007.Z + Exp007.X) (Exp009.infiniteSolution a t x) := by
  rw [infiniteSolution_time_derivative a ha t x,
    infiniteSolution_second_derivative a ha t x]
  have hu := Exp009.modeSolution_summable a (regular_absolute a ha) t x
  have ht := regular_time_summable a ha t x
  have hxx := regular_second_summable a ha t x
  have hv := hu.mapL (operatorOf (Exp007.Z + Exp007.X))
  rw [← ht.tsum_const_smul Complex.I, ← tsum_neg,
    Exp009.infiniteSolution, (operatorOf (Exp007.Z + Exp007.X)).map_tsum hu,
    ← hxx.neg.tsum_add hv]
  exact tsum_congr fun m => mode_schrodinger m (a m) t x

end NDEAEvolve.Exp010
