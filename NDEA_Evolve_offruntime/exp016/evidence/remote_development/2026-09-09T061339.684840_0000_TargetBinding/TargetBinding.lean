import IndependentTarget
import ActualCayleySynthesis
import VariablePotentialBridge

/-! Explicit binding of the implementation to the independently specified
actual ordered recurrence and physical reconstruction. The final theorem
applies Exp015 to that identified field, with a derived residual budget.
It does not claim spatial refinement or validated floating-point computation. -/
noncomputable section
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

theorem fourierReconstruction_eq_independentTarget (M : ℕ) (h : ℝ)
    (y : Vec (Grid (2*M))) :
    fourierReconstruction M h y = IndependentTarget.rawFourier M h y := by
  funext x
  simp only [fourierReconstruction, fourierSynthesis, fourierCoefficient,
    oddFrequency, IndependentTarget.rawFourier, Int.cast_sub, Int.cast_natCast]

theorem actualFourierQuadratic_eq_independentTarget (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2*M)) (Grid (2*M)) ℂ)
    (y : Vec (Grid (2*M))) (t₀ k : ℝ) :
    actualFourierQuadratic M h A B y t₀ k =
      IndependentTarget.actualCayleyFourierSlab M h A B y t₀ k := by
  funext t x
  unfold actualFourierQuadratic IndependentTarget.actualCayleyFourierSlab
  rw [fourierReconstruction_eq_independentTarget]
  rfl

theorem actualFourierQuadratic_realizes_target (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2*M)) (Grid (2*M)) ℂ)
    (y : Vec (Grid (2*M))) (t₀ k : ℝ) :
    IndependentTarget.RealizesActualCayleySlab M h A B y t₀ k
      (actualFourierQuadratic M h A B y t₀ k) := by
  intro t x
  exact congrFun (congrFun (actualFourierQuadratic_eq_independentTarget M h A B y t₀ k) t) x

theorem independentTarget_regular (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2*M)) (Grid (2*M)) ℂ)
    (y : Vec (Grid (2*M))) (t₀ k : ℝ) :
    Exp015.IsRegularPeriodicField (2*Real.pi)
      (IndependentTarget.actualCayleyFourierSlab M h A B y t₀ k) := by
  rw [← actualFourierQuadratic_eq_independentTarget]
  exact actualFourierQuadratic_regular M h A B y t₀ k

theorem independentTarget_spatialL2 (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (y : Vec (Grid (2*M))) (b : ℝ) :
    Exp015.spatialL2 (IndependentTarget.rawFourier M h y) b (2*Real.pi) =
      Real.sqrt h * ‖y‖ := by
  rw [← fourierReconstruction_eq_independentTarget]
  exact fourierReconstruction_spatialL2 M h hmesh y b

theorem independentTarget_actual_residual_budget (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (A B : Matrix (Grid (2*M)) (Grid (2*M)) ℂ)
    (V : ℝ → E 2 →L[ℂ] E 2) (hV : Continuous V)
    (y : Vec (Grid (2*M))) (b t₀ k t : ℝ)
    (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ht : t ∈ Icc t₀ (t₀+k)) :
    Exp015.spatialL2 (Exp015.pdeResidual (fun _ => V)
      (IndependentTarget.actualCayleyFourierSlab M h A B y t₀ k) t) b (2*Real.pi) ≤
      actualFourierResidualBudget M h A B V y b k := by
  rw [← actualFourierQuadratic_eq_independentTarget]
  exact actualFourierQuadratic_residual_spatialL2_le M h hmesh A B V hV y b t₀ k t
    hk hA hB ht

/-- The target field from the actual ordered stages has a proved error
certificate against Exp014's solution. The initial mismatch is unrestricted,
and the observation time may lie in the final partial slab. -/
theorem independentTarget_variable_potential_slab_error (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (A B : Matrix (Grid (2*M)) (Grid (2*M)) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y : Vec (Grid (2*M))) (b t₀ k t : ℝ) (hk : 0 < k)
    (ht : t ∈ Icc t₀ (t₀+k)) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.actualCayleyFourierSlab M h A B y t₀ k t x -
        Exp014.solution v a t x) b (2*Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y x -
        Exp014.solution v a t₀ x) b (2*Real.pi) +
      (t-t₀)*actualFourierResidualBudget M h A B (Exp014.operatorPotential v) y b k := by
  let w := IndependentTarget.actualCayleyFourierSlab M h A B y t₀ k
  have hw := independentTarget_regular M h A B y t₀ k
  have hVc := Exp014.operatorPotential_continuous v hv
  have hr := Exp015.pdeResidual_continuous (fun _ => Exp014.operatorPotential v) w hw
    (hVc.comp continuous_snd)
  have hb : ∀ r ∈ Icc t₀ t,
      Exp015.spatialL2 (Exp015.pdeResidual (fun _ => Exp014.operatorPotential v) w r)
        b (2*Real.pi) ≤ actualFourierResidualBudget M h A B (Exp014.operatorPotential v) y b k := by
    intro r hr
    exact independentTarget_actual_residual_budget M h hmesh A B _ hVc y b t₀ k r
      hk.ne' hA hB ⟨hr.1, hr.2.trans ht.2⟩
  have he := Exp015.residual_error_uniform_budget w (Exp014.solution v a) hw
    (Exp014.solution_classical v hv a)
    (fun _ x => Exp014.operatorPotential_selfAdjoint v hHerm x)
    (by positivity : 0 < 2*Real.pi) hr b t₀ t _ ht.1 hb
  have hi : w t₀ = IndependentTarget.rawFourier M h y := by
    funext x
    have hl := actualFourierQuadratic_left M h A B y t₀ k x hk.ne'
    rw [actualFourierQuadratic_eq_independentTarget, fourierReconstruction_eq_independentTarget] at hl
    exact hl
  rw [hi] at he
  exact he

#print axioms fourierReconstruction_eq_independentTarget
#print axioms actualFourierQuadratic_eq_independentTarget
#print axioms actualFourierQuadratic_realizes_target
#print axioms independentTarget_regular
#print axioms independentTarget_spatialL2
#print axioms independentTarget_actual_residual_budget
#print axioms independentTarget_variable_potential_slab_error
end NDEAEvolve.Exp016
