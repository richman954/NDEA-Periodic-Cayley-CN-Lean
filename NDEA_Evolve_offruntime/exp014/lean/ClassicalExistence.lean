import FourierProduct
import GlobalLinearEvolution
import GenericUniqueness

/-! Global existence of the actual classical periodic PDE from regular Fourier
data and a regular spatially varying potential. The trajectory is constructed
by the Dyson evolution in the interaction picture; the classical PDE is then
derived from bounded synthesis and actual differentiation. -/
noncomputable section
open scoped BigOperators Topology
namespace NDEAEvolve.Exp014

private theorem synthesis_along_continuous_state
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (S : E → ℝ → F) (hS : Continuous (fun p : ℝ × E => S p.2 p.1))
    (q : ℝ → E) (hq : Continuous q) :
    Continuous (fun p : ℝ × ℝ => S (q p.1) p.2) :=
  hS.comp (continuous_snd.prodMk (hq.comp continuous_fst))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def interactionGenerator (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    FourierState H →L[ℂ] FourierState H :=
  (-Complex.I) • (freeFlow (-t)).comp ((potentialConvolution v).comp (freeFlow t))

theorem interactionGenerator_apply (v : ℤ → H →L[ℂ] H) (t : ℝ) (b : FourierState H) :
    interactionGenerator v t b =
      (-Complex.I) • freeFlow (-t) (potentialConvolution v (freeFlow t b)) := rfl

theorem interactionGenerator_bound (v : ℤ → H →L[ℂ] H) (t : ℝ) (b : FourierState H) :
    ‖interactionGenerator v t b‖ ≤ ‖potentialConvolution v‖ * ‖b‖ := by
  rw [interactionGenerator_apply, norm_smul, norm_neg, Complex.norm_I, one_mul, freeFlow_norm]
  simpa only [freeFlow_norm] using (potentialConvolution v).le_opNorm (freeFlow t b)

theorem interactionGenerator_joint_continuous (v : ℤ → H →L[ℂ] H) :
    Continuous (fun p : ℝ × FourierState H => interactionGenerator v p.1 p.2) := by
  have hc := (potentialConvolution v).continuous.comp freeFlow_joint_continuous
  exact (freeFlow_joint_continuous.comp (continuous_fst.neg.prodMk hc)).const_smul (-Complex.I)

def interactionReal (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    FourierState H →L[ℝ] FourierState H := (interactionGenerator v t).restrictScalars ℝ

theorem interactionReal_norm_le (v : ℤ → H →L[ℂ] H) (t : ℝ) :
    ‖interactionReal v t‖ ≤ ‖potentialConvolution v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (potentialConvolution v).opNorm_nonneg
    (interactionGenerator_bound v t)

def interactingState (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) : ℝ → FourierState H :=
  linearEvolution (interactionReal v) b₀

theorem interactingState_zero (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    interactingState v b₀ 0 = b₀ :=
  linearEvolution_zero (interactionReal v) ‖potentialConvolution v‖₊
    (interactionReal_norm_le v) b₀

theorem interactingState_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t : ℝ) :
    HasDerivAt (interactingState v b₀)
      (interactionGenerator v t (interactingState v b₀ t)) t :=
  linearEvolution_hasDerivAt (interactionReal v) (interactionGenerator_joint_continuous v)
    ‖potentialConvolution v‖₊ (interactionReal_norm_le v) b₀ t

theorem interactingState_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (interactingState v b₀) :=
  continuous_iff_continuousAt.mpr fun t => (interactingState_hasDerivAt v b₀ t).continuousAt

def physicalState (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t : ℝ) : FourierState H :=
  freeFlow t (interactingState v b₀ t)

theorem physicalState_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (physicalState v b₀) :=
  freeFlow_joint_continuous.comp (continuous_id.prodMk (interactingState_continuous v b₀))

def solution (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) : H :=
  synth (physicalState v b₀ t) x

theorem solution_zero (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (x : ℝ) :
    solution v b₀ 0 x = synth b₀ x := by
  simp [solution, physicalState, interactingState_zero, freeFlow_zero]

theorem solution_continuous (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) :
    Continuous (fun p : ℝ × ℝ => solution v b₀ p.1 p.2) :=
  synthesis_along_continuous_state (synth (H := H)) (synth_joint_continuous (H := H))
    (physicalState v b₀) (physicalState_continuous v b₀)

theorem solution_space_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (solution v b₀ t) (synthFirst (physicalState v b₀ t) x) x :=
  synth_hasDerivAt (physicalState v b₀ t) x

theorem solution_second_hasDerivAt (v : ℤ → H →L[ℂ] H) (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (deriv (solution v b₀ t)) (synthSecond (physicalState v b₀ t) x) x := by
  have h : deriv (solution v b₀ t) = synthFirst (physicalState v b₀ t) :=
    funext fun y => (solution_space_hasDerivAt v b₀ t y).deriv
  rw [h]
  exact synthFirst_hasDerivAt (physicalState v b₀ t) x

theorem solution_time_hasDerivAt (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b₀ : FourierState H) (t x : ℝ) :
    HasDerivAt (fun s => solution v b₀ s x)
      (Complex.I • synthSecond (physicalState v b₀ t) x +
        (-Complex.I) • operatorPotential v x (solution v b₀ t x)) t := by
  let A : ℝ → FourierState H →L[ℝ] H :=
    fun s => ((synthesisCLM x).comp (freeFlow s)).restrictScalars ℝ
  have hA : Continuous (fun p : ℝ × FourierState H => A p.1 p.2) :=
    (synthesisCLM x).continuous.comp freeFlow_joint_continuous
  have h := strong_apply_hasDerivAt A hA (interactingState v b₀)
    (interactionGenerator v t (interactingState v b₀ t))
    (Complex.I • synthSecond (physicalState v b₀ t) x) t
    (interactingState_hasDerivAt v b₀ t)
    (synth_freeFlow_hasDerivAt (interactingState v b₀ t) t x)
  have he : A t (interactionGenerator v t (interactingState v b₀ t)) =
      (-Complex.I) • operatorPotential v x (solution v b₀ t x) := by
    change synth (freeFlow t ((-Complex.I) • freeFlow (-t)
      (potentialConvolution v (freeFlow t (interactingState v b₀ t))))) x = _
    rw [map_smul, ← freeFlow_add, add_neg_cancel, freeFlow_zero]
    change synthesisCLM x ((-Complex.I) • potentialConvolution v (physicalState v b₀ t)) = _
    rw [map_smul]
    exact congrArg ((-Complex.I) • ·) (synth_potentialConvolution v hv (physicalState v b₀ t) x)
  rw [he] at h
  have hfun : (fun s => A s (interactingState v b₀ s)) =
      (fun s => solution v b₀ s x) := by
    funext s
    rfl
  rw [hfun, add_comm] at h
  exact h

theorem solution_classical (v : ℤ → H →L[ℂ] H) (hv : RegularPotential v)
    (b₀ : FourierState H) :
    Exp013.IsClassicalPeriodicSolution (2 * Real.pi) (fun _ x => operatorPotential v x)
      0 (solution v b₀) where
  time_differentiable t x := (solution_time_hasDerivAt v hv b₀ t x).differentiableAt
  space_differentiable t x := (solution_space_hasDerivAt v b₀ t x).differentiableAt
  second_space_differentiable t x := (solution_second_hasDerivAt v b₀ t x).differentiableAt
  continuous_solution := solution_continuous v b₀
  continuous_time_derivative := by
    have hsecond : Continuous (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthSecond (H := H)) (synthSecond_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have hvu : Continuous (fun p : ℝ × ℝ =>
        operatorPotential v p.2 (solution v b₀ p.1 p.2)) :=
      ((operatorPotential_continuous v hv).comp continuous_snd).clm_apply
        (solution_continuous v b₀)
    have h := (hsecond.const_smul Complex.I).add (hvu.const_smul (-Complex.I))
    have he : (fun p : ℝ × ℝ => deriv (fun s => solution v b₀ s p.2) p.1) =
        (fun p : ℝ × ℝ => Complex.I • synthSecond (physicalState v b₀ p.1) p.2 +
          (-Complex.I) • operatorPotential v p.2 (solution v b₀ p.1 p.2)) :=
      funext fun p => (solution_time_hasDerivAt v hv b₀ p.1 p.2).deriv
    rw [he]
    exact h
  continuous_space_derivative := by
    have h : Continuous (fun p : ℝ × ℝ => synthFirst (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthFirst (H := H)) (synthFirst_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have he : (fun p : ℝ × ℝ => deriv (solution v b₀ p.1) p.2) =
        (fun p : ℝ × ℝ => synthFirst (physicalState v b₀ p.1) p.2) :=
      funext fun p => (solution_space_hasDerivAt v b₀ p.1 p.2).deriv
    rw [he]
    exact h
  continuous_second_derivative := by
    have h : Continuous (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      synthesis_along_continuous_state (synthSecond (H := H)) (synthSecond_joint_continuous (H := H))
        (physicalState v b₀) (physicalState_continuous v b₀)
    have he : (fun p : ℝ × ℝ => deriv (deriv (solution v b₀ p.1)) p.2) =
        (fun p : ℝ × ℝ => synthSecond (physicalState v b₀ p.1) p.2) :=
      funext fun p => (solution_second_hasDerivAt v b₀ p.1 p.2).deriv
    rw [he]
    exact h
  periodic t := synth_periodic (physicalState v b₀ t)
  schrodinger t x := by
    rw [(solution_time_hasDerivAt v hv b₀ t x).deriv,
      (solution_second_hasDerivAt v b₀ t x).deriv]
    simp only [Pi.zero_apply, add_zero, smul_add, smul_smul, mul_neg,
      Complex.I_mul_I, neg_neg, neg_one_smul, one_smul]

theorem global_classical_exists_unique (v : ℤ → H →L[ℂ] H)
    (hv : RegularPotential v) (hHerm : HermitianFourierPotential v)
    (a : ℤ → H) (ha : Summable (fun m => weight m * ‖a m‖)) :
    ∃! u : ℝ → ℝ → H,
      Exp013.IsClassicalPeriodicSolution (2 * Real.pi) (fun _ x => operatorPotential v x) 0 u ∧
      ∀ x, u 0 x = ∑' m, character x m • a m := by
  let b₀ := ofCoefficients a ha
  have hi : ∀ x, solution v b₀ 0 x = ∑' m, character x m • a m := by
    intro x
    rw [solution_zero, synth_eq_tsum]
    simp only [b₀, coefficient_ofCoefficients]
  refine ⟨solution v b₀, ⟨solution_classical v hv b₀, hi⟩, ?_⟩
  intro u hu
  apply Exp013.classical_unique (by positivity : 0 < 2 * Real.pi) u (solution v b₀)
    hu.1 (solution_classical v hv b₀) (fun _ x => operatorPotential_selfAdjoint v hHerm x)
  intro x
  exact (hu.2 x).trans (hi x).symm

end NDEAEvolve.Exp014
