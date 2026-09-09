import SpatialDefectSplit
import FourierNorm
import FullBandSymbol

/-! Exact full-grid diagonalization of the actual centered Laplacian, followed
by the Fourier expression and L2 bound for its continuum spatial defect.
The bound retains the actual fourth frequency moment of the grid state.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

private theorem stencil_frequency_bound (M : ℕ) (m : Fin (2 * M + 1)) :
    |(oddFrequency M m : ℝ)| ≤ (M : ℝ) := by
  have hm : m.val ≤ 2 * M := Nat.le_of_lt_succ m.isLt
  have hmR : (m.val : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m.val := Nat.cast_nonneg _
  simp only [oddFrequency, Int.cast_sub, Int.cast_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The existing full-band DFT extracts the coefficient of each resolved mode. -/
theorem fourierCoefficient_modeLift (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (m l : Fin (2 * M + 1)) (u : E 2) :
    fourierCoefficient M h (modeLiftCLM (2 * M) h (oddFrequency M m) u) l =
      if m = l then u else 0 := by
  classical
  have hN : ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 * M + 1 ≠ 0 by omega)
  have hn (j : Fin (2 * M + 1)) :
      Exp011.nodeValue (2 * M) (modeLiftCLM (2 * M) h (oddFrequency M m) u) j =
        phase ((oddFrequency M m : ℝ) * ((j.val : ℝ) * h)) • u := by
    ext a
    rfl
  have hp (j : Fin (2 * M + 1)) :
      phase (-((oddFrequency M l : ℝ) * ((j.val : ℝ) * h))) *
          phase ((oddFrequency M m : ℝ) * ((j.val : ℝ) * h)) =
        phase (((oddFrequency M m - oddFrequency M l : ℤ) : ℝ) * ((j.val : ℝ) * h)) := by
    rw [← phase_add]
    congr 1
    push_cast
    ring
  unfold fourierCoefficient
  simp_rw [hn, smul_smul, hp]
  rw [← Finset.sum_smul]
  by_cases hml : m = l
  · subst l
    simp only [sub_self, Int.cast_zero, zero_mul, phase_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_smul, inv_mul_cancel₀ hN, one_smul, ite_true]
  · have hnd : ¬ ((2 * M + 1 : ℕ) : ℤ) ∣ oddFrequency M m - oddFrequency M l :=
      band_difference_not_dvd M (2 * M) (oddFrequency M l) (oddFrequency M m)
        (stencil_frequency_bound M l) (stencil_frequency_bound M m) (by omega)
        (fun he => hml ((oddFrequency_injective M he).symm))
    rw [phase_sum_zero (2 * M) h hmesh _ hnd, zero_smul, smul_zero, if_neg hml]

/-- Sampling fidelity decomposes arbitrary grid data into the saved lifted modes. -/
theorem gridState_eq_modeLift_sum (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) :
    y = ∑ m : Fin (2 * M + 1),
      modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m) := by
  calc
    y = Exp010.sampleSolution (2 * M) h (fun _ => fourierReconstruction M h y) 0 :=
      (sampleSolution_fourierReconstruction M h hmesh y).symm
    _ = _ := by
      ext p
      simp [Exp010.sampleSolution, fourierReconstruction, fourierSynthesis,
        modeLiftCLM, modeLiftLinear, modeLift]

/-- The actual positive grid Laplacian is diagonal on every resolved frequency. -/
theorem fourierCoefficient_gridKinetic (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) (l : Fin (2 * M + 1)) :
    fourierCoefficient M h (op (gridKinetic (2 * M) h) y) l =
      (modeSymbol (oddFrequency M l) h : ℂ) • fourierCoefficient M h y l := by
  classical
  rw [← fourierCoefficientCLM_apply M h l (op (gridKinetic (2 * M) h) y)]
  calc
    _ = fourierCoefficientCLM M h l (op (gridKinetic (2 * M) h)
        (∑ m : Fin (2 * M + 1),
          modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m))) :=
      congrArg (fun z => fourierCoefficientCLM M h l (op (gridKinetic (2 * M) h) z))
        (gridState_eq_modeLift_sum M h hmesh y)
    _ = ∑ m : Fin (2 * M + 1), (modeSymbol (oddFrequency M m) h : ℂ) •
        fourierCoefficient M h
          (modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m)) l := by
      simp only [map_sum, gridKinetic, laplacian_modeLift (2 * M) h _ hmesh,
        map_smul, fourierCoefficientCLM_apply]
    _ = _ := by
      simp only [fourierCoefficient_modeLift M h hmesh]
      simp

theorem fourierReconstruction_gridKinetic (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) (x : ℝ) :
    fourierReconstruction M h (op (gridKinetic (2 * M) h) y) x =
      fourierSynthesis M (fun m =>
        (modeSymbol (oddFrequency M m) h : ℂ) • fourierCoefficient M h y m) x := by
  simp only [fourierReconstruction, fourierSynthesis, fourierCoefficient_gridKinetic M h hmesh]

/-- The sign is λ_h(m)−m² because the continuum second derivative contributes −m². -/
theorem sampledStencilDefect_eq_synthesis (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) (x : ℝ) :
    sampledStencilDefect M h x y =
      fourierSynthesis M (fun m =>
        ((modeSymbol (oddFrequency M m) h - (oddFrequency M m : ℝ) ^ 2 : ℝ) : ℂ) •
          fourierCoefficient M h y m) x := by
  change fourierEval M h x (op (gridKinetic (2 * M) h) y) + fourierDxx M h x y = _
  rw [fourierEval_apply, fourierReconstruction_gridKinetic M h hmesh]
  simp only [fourierDxx, _root_.sum_apply, _root_.smul_apply,
    fourierCoefficientCLM_apply, fourierSynthesis]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [smul_smul, ← add_smul]
  congr 1
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- A quantitative full-band estimate retaining the computed fourth moment.
No uniform moment bound or refinement limit is supplied as an assumption. -/
theorem sampledStencilDefect_spatialL2_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (y : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => sampledStencilDefect M h x y) b (2 * Real.pi) ≤
      Real.sqrt (2 * Real.pi) * h ^ 2 *
        Real.sqrt (∑ m : Fin (2 * M + 1),
          ((oddFrequency M m : ℝ) ^ 4 * ‖fourierCoefficient M h y m‖) ^ 2) := by
  have hh : 0 < h := by
    have hN : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by positivity
    nlinarith [Real.pi_pos]
  let a := fourierCoefficient M h y
  let δ := fun m : Fin (2 * M + 1) => modeSymbol (oddFrequency M m) h - (oddFrequency M m : ℝ) ^ 2
  have hterm (m : Fin (2 * M + 1)) :
      ‖((δ m : ℝ) : ℂ) • a m‖ ≤
        h ^ 2 * ((oddFrequency M m : ℝ) ^ 4 * ‖a m‖) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |δ m| * ‖a m‖ ≤ (h ^ 2 * (oddFrequency M m : ℝ) ^ 4) * ‖a m‖ :=
        mul_le_mul_of_nonneg_right (modeSymbol_consistency_fullBand (oddFrequency M m) h hh)
          (norm_nonneg _)
      _ = _ := by ring
  have hs : (∑ m : Fin (2 * M + 1), ‖((δ m : ℝ) : ℂ) • a m‖ ^ 2) ≤
      ∑ m : Fin (2 * M + 1),
        (h ^ 2 * ((oddFrequency M m : ℝ) ^ 4 * ‖a m‖)) ^ 2 := by
    apply Finset.sum_le_sum
    intro m _
    exact pow_le_pow_left₀ (norm_nonneg _) (hterm m) 2
  have he : (fun x => sampledStencilDefect M h x y) =
      fourierSynthesis M (fun m => ((δ m : ℝ) : ℂ) • a m) :=
    funext (sampledStencilDefect_eq_synthesis M h hmesh y)
  rw [he, fourierSynthesis_spatialL2]
  calc
    _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (∑ m : Fin (2 * M + 1),
        (h ^ 2 * ((oddFrequency M m : ℝ) ^ 4 * ‖a m‖)) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (Real.sqrt_nonneg _)
    _ = _ := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg (h ^ 2)),
        Real.sqrt_sq (sq_nonneg h)]
      dsimp only [a]
      ring

#print axioms fourierCoefficient_modeLift
#print axioms gridState_eq_modeLift_sum
#print axioms fourierCoefficient_gridKinetic
#print axioms fourierReconstruction_gridKinetic
#print axioms sampledStencilDefect_eq_synthesis
#print axioms sampledStencilDefect_spatialL2_le
end NDEAEvolve.Exp016
