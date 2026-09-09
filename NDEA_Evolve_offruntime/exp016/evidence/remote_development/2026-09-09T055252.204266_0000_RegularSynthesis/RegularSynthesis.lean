import ResidualField
import QuadraticTime
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Actual derivative and residual transport through regular spatial synthesis.
The contract contains regularity only, never a consistency or refinement premise. -/
noncomputable section
namespace NDEAEvolve.Exp016

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure RegularSynthesis (E H : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (L : ℝ) where
  eval : ℝ → E →L[ℂ] H
  dx : ℝ → E →L[ℂ] H
  dxx : ℝ → E →L[ℂ] H
  continuous_eval : Continuous eval
  continuous_dx : Continuous dx
  continuous_dxx : Continuous dxx
  derivative_eval : ∀ x z, HasDerivAt (fun y => eval y z) (dx x z) x
  derivative_dx : ∀ x z, HasDerivAt (fun y => dx y z) (dxx x z) x
  periodic_eval : Function.Periodic eval L

namespace RegularSynthesis
variable {L : ℝ} (S : RegularSynthesis E H L)

def field (q : ℝ → E) (t x : ℝ) : H := S.eval x (q t)

theorem field_time_hasDerivAt (q : ℝ → E) (q' : E) (t x : ℝ)
    (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => S.field q s x) (S.eval x q') t := by
  simpa only [field, Function.comp_apply] using!
    ((S.eval x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hq

theorem field_time_derivative (q : ℝ → E) (q' : E) (t x : ℝ)
    (hq : HasDerivAt q q' t) :
    deriv (fun s => S.field q s x) t = S.eval x q' :=
  (S.field_time_hasDerivAt q q' t x hq).deriv

theorem field_space_derivative (q : ℝ → E) (t x : ℝ) :
    deriv (S.field q t) x = S.dx x (q t) := (S.derivative_eval x (q t)).deriv

theorem field_second_space_derivative (q : ℝ → E) (t x : ℝ) :
    deriv (deriv (S.field q t)) x = S.dxx x (q t) := by
  have h : deriv (S.field q t) = fun y => S.dx y (q t) :=
    funext (S.field_space_derivative q t)
  rw [h]
  exact (S.derivative_dx x (q t)).deriv

theorem field_regular (q q' : ℝ → E) (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq' : Continuous q') : Exp015.IsRegularPeriodicField L (S.field q) := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun t => (hq t).continuousAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    exact (S.field_time_hasDerivAt q (q' t) t x (hq t)).differentiableAt
  · intro t x
    exact (S.derivative_eval x (q t)).differentiableAt
  · intro t x
    have h : deriv (S.field q t) = fun y => S.dx y (q t) :=
      funext (S.field_space_derivative q t)
    rw [h]
    exact (S.derivative_dx x (q t)).differentiableAt
  · exact (S.continuous_eval.comp continuous_snd).clm_apply (hqc.comp continuous_fst)
  · simp_rw [S.field_time_derivative q _ _ _ (hq _)]
    exact (S.continuous_eval.comp continuous_snd).clm_apply (hq'.comp continuous_fst)
  · simp_rw [S.field_space_derivative]
    exact (S.continuous_dx.comp continuous_snd).clm_apply (hqc.comp continuous_fst)
  · simp_rw [S.field_second_space_derivative]
    exact (S.continuous_dxx.comp continuous_snd).clm_apply (hqc.comp continuous_fst)
  · intro t x
    change S.eval (x + L) (q t) = S.eval x (q t)
    rw [S.periodic_eval x]

/-- The computed spatial discrepancy, including the actual second derivative. -/
def spatialDefect (G : E →L[ℂ] E) (V : ℝ → H →L[ℂ] H) (x : ℝ) : E →L[ℂ] H :=
  (S.eval x).comp G + S.dxx x - (V x).comp (S.eval x)

theorem field_residual (G : E →L[ℂ] E) (V : ℝ → H →L[ℂ] H)
    (q : ℝ → E) (q' : E) (t x : ℝ) (hq : HasDerivAt q q' t) :
    Exp015.pdeResidual (fun _ => V) (S.field q) t x =
      S.eval x (Complex.I • q' - G (q t)) + S.spatialDefect G V x (q t) := by
  rw [Exp015.pdeResidual, S.field_time_derivative q q' t x hq,
    S.field_second_space_derivative]
  simp only [spatialDefect, field, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul]
  module

theorem quadratic_field_regular (G : E →L[ℂ] E) (m v : E) (t₀ k : ℝ) :
    Exp015.IsRegularPeriodicField L (S.field (quadraticTime G m v t₀ k)) := by
  apply S.field_regular _ (fun t => v - (Complex.I * (quadraticOffset t₀ k t : ℂ)) • G v)
    (fun t => quadraticTime_hasDerivAt G m v t₀ k t)
  unfold quadraticOffset
  fun_prop

theorem quadratic_field_residual (G : E →L[ℂ] E) (V : ℝ → H →L[ℂ] H)
    (m v : E) (t₀ k t x : ℝ) :
    Exp015.pdeResidual (fun _ => V) (S.field (quadraticTime G m v t₀ k)) t x =
      S.eval x (Complex.I • v - G m) +
        quadraticCorrection t₀ k t • S.eval x (G (G v)) +
        S.spatialDefect G V x (quadraticTime G m v t₀ k t) := by
  rw [S.field_residual G V _ _ t x (quadraticTime_hasDerivAt G m v t₀ k t)]
  have h := quadraticTime_gridResidual G m v t₀ k t
  rw [quadraticTime_derivative] at h
  rw [h, map_add, map_smul]

theorem quadratic_slab_left (G : E →L[ℂ] E) (u₀ u₁ : E) (t₀ k x : ℝ) (hk : k ≠ 0) :
    S.field (quadraticSlab G u₀ u₁ t₀ k) t₀ x = S.eval x u₀ := by
  rw [field, quadraticSlab_left G u₀ u₁ t₀ k hk]

theorem quadratic_slab_right (G : E →L[ℂ] E) (u₀ u₁ : E) (t₀ k x : ℝ) (hk : k ≠ 0) :
    S.field (quadraticSlab G u₀ u₁ t₀ k) (t₀ + k) x = S.eval x u₁ := by
  rw [field, quadraticSlab_right G u₀ u₁ t₀ k hk]

/-- Immediate regular instance for the zero Fourier mode / one-node reconstruction. -/
def constant (J : E →L[ℂ] H) (L : ℝ) : RegularSynthesis E H L where
  eval := fun _ => J
  dx := fun _ => 0
  dxx := fun _ => 0
  continuous_eval := continuous_const
  continuous_dx := continuous_const
  continuous_dxx := continuous_const
  derivative_eval := by intro x z; exact hasDerivAt_const x (J z)
  derivative_dx := by intro x z; exact hasDerivAt_const x (0 : H)
  periodic_eval := fun _ => rfl

#print axioms field_time_hasDerivAt
#print axioms field_time_derivative
#print axioms field_space_derivative
#print axioms field_second_space_derivative
#print axioms field_regular
#print axioms field_residual
#print axioms quadratic_field_regular
#print axioms quadratic_field_residual
#print axioms quadratic_slab_left
#print axioms quadratic_slab_right

end RegularSynthesis
end NDEAEvolve.Exp016
