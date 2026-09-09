import ClassicalSolution

/-! Joint continuity of the solution and its actual classical derivatives.
The global second-moment majorant covers the entire time-space plane. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
namespace NDEAEvolve.Exp010

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

theorem modeSpace_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSpace m v p.1 p.2) :=
  (modeSolution_continuous m v).const_smul (Complex.I * (m : ℂ))

theorem modeSecond_continuous (m : ℤ) (v : E 2) :
    Continuous (fun p : ℝ × ℝ => modeSecond m v p.1 p.2) :=
  (modeSolution_continuous m v).const_smul (-((m : ℂ)^2))

/-- Absolute summability alone already gives joint continuity of the solution. -/
theorem infiniteSolution_continuous_of_absolute (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    Continuous (fun p : ℝ × ℝ => Exp009.infiniteSolution a p.1 p.2) := by
  exact continuous_tsum (fun m => modeSolution_continuous m (a m)) ha
    (fun m p => le_of_eq (modeSolution_norm m (a m) p.1 p.2))

theorem infiniteSolution_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => Exp009.infiniteSolution a p.1 p.2) :=
  infiniteSolution_continuous_of_absolute a (regular_absolute a ha)

theorem infiniteSolution_time_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => Exp009.infiniteSolution a s p.2) p.1) := by
  have he : (fun p : ℝ × ℝ => deriv (fun s => Exp009.infiniteSolution a s p.2) p.1) =
      fun p => ∑' m, modeTime m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_time_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeTime_continuous m (a m))
    (regular_time_majorant a ha)
    (fun m p => modeTime_norm_le m (a m) p.1 p.2)

theorem infiniteSolution_space_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (Exp009.infiniteSolution a p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (Exp009.infiniteSolution a p.1) p.2) =
      fun p => ∑' m, modeSpace m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_space_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeSpace_continuous m (a m)) ha
    (fun m p => modeSpace_norm_le m (a m) p.1 p.2)

theorem infiniteSolution_second_derivative_continuous (a : ℤ → E 2) (ha : Regular a) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (Exp009.infiniteSolution a p.1)) p.2) := by
  have he : (fun p : ℝ × ℝ => deriv (deriv (Exp009.infiniteSolution a p.1)) p.2) =
      fun p => ∑' m, modeSecond m (a m) p.1 p.2 :=
    funext fun p => infiniteSolution_second_derivative a ha p.1 p.2
  rw [he]
  exact continuous_tsum (fun m => modeSecond_continuous m (a m)) ha
    (fun m p => modeSecond_norm_le m (a m) p.1 p.2)

/-- Classical periodic solution of the spinor equation. Derivative existence is
included explicitly because Lean's `deriv` is a totalized operation. -/
structure IsClassicalPeriodicSolution (u : ℝ → ℝ → E 2) : Prop where
  time_differentiable : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space_differentiable : ∀ t x, DifferentiableAt ℝ (u t) x
  second_space_differentiable : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x
  continuous_solution : Continuous (fun p : ℝ × ℝ => u p.1 p.2)
  continuous_time_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1)
  continuous_space_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)
  continuous_second_derivative :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (u p.1)) p.2)
  periodic : ∀ t, Function.Periodic (u t) (2 * Real.pi)
  schrodinger : ∀ t x, Complex.I • deriv (fun s => u s x) t =
    -deriv (deriv (u t)) x + operatorOf (Exp007.Z + Exp007.X) (u t x)

/-- A finite second weighted Fourier moment gives a classical periodic solution
with actual time and space derivatives and the pointwise PDE. -/
theorem infiniteSolution_classical (a : ℤ → E 2) (ha : Regular a) :
    IsClassicalPeriodicSolution (Exp009.infiniteSolution a) where
  time_differentiable t x := (infiniteSolution_time_hasDerivAt a ha t x).differentiableAt
  space_differentiable t x := (infiniteSolution_space_hasDerivAt a ha t x).differentiableAt
  second_space_differentiable t x :=
    (infiniteSolution_second_hasDerivAt a ha t x).differentiableAt
  continuous_solution := infiniteSolution_continuous a ha
  continuous_time_derivative := infiniteSolution_time_derivative_continuous a ha
  continuous_space_derivative := infiniteSolution_space_derivative_continuous a ha
  continuous_second_derivative := infiniteSolution_second_derivative_continuous a ha
  periodic := Exp009.infiniteSolution_periodic a
  schrodinger := infiniteSolution_schrodinger a ha

end NDEAEvolve.Exp010
