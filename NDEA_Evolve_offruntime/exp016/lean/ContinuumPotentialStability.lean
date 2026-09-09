import SpatialL2Operator
import VariablePotentialBridge

/-! Continuum stability for two actual Exp014 variable-potential solutions.
The residual of the second solution in the first equation is calculated from
its classical derivatives. Its forcing norm is bounded using conserved
physical L2 mass, without a bound on evolving weighted Fourier norms. -/
noncomputable section
open MeasureTheory
namespace NDEAEvolve.Exp016

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual derivative residual has the ordered sign W - V. Only the
potential whose solution is differentiated needs regularity for this identity. -/
theorem solution_pdeResidual_other_potential (v w : ℤ → H →L[ℂ] H)
    (hw : Exp014.RegularPotential w) (a : Exp014.FourierState H) (t x : ℝ) :
    Exp015.pdeResidual (fun _ y => Exp014.operatorPotential v y)
      (Exp014.solution w a) t x =
      (Exp014.operatorPotential w x - Exp014.operatorPotential v x)
        (Exp014.solution w a t x) := by
  unfold Exp015.pdeResidual
  rw [(Exp014.solution_classical w hw a).schrodinger t x]
  simp only [Pi.zero_apply, add_zero, sub_apply]
  abel

/-- Exp013's exact energy conservation applies to the constructed solution.
The conserved norm is the physical norm of the synthesized initial datum. -/
theorem solution_spatialL2_conserved (v : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hHerm : Exp014.HermitianFourierPotential v)
    (a : Exp014.FourierState H) (b t : ℝ) :
    Exp015.spatialL2 (Exp014.solution v a t) b (2 * Real.pi) =
      Exp015.spatialL2 (Exp014.synth a) b (2 * Real.pi) := by
  have he := congrArg Real.sqrt (Exp013.energy_eq_initial (Exp014.solution v a)
    (Exp014.solution_classical v hv a)
    (fun _ x => Exp014.operatorPotential_selfAdjoint v hHerm x) b t)
  change Exp015.spatialL2 (Exp014.solution v a t) b (2 * Real.pi) =
    Exp015.spatialL2 (Exp014.solution v a 0) b (2 * Real.pi) at he
  have hi : Exp014.solution v a 0 = Exp014.synth a :=
    funext fun x => Exp014.solution_zero v a x
  rw [hi] at he
  exact he

private theorem cps_spatialL2_sub_comm (u z : ℝ → H) (b L : ℝ) :
    Exp015.spatialL2 (fun x => u x - z x) b L =
      Exp015.spatialL2 (fun x => z x - u x) b L := by
  unfold Exp015.spatialL2
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  change ‖u x - z x‖ ^ 2 = ‖z x - u x‖ ^ 2
  rw [norm_sub_rev]

/-- Uniform operator-potential perturbation costs exactly t * delta times
the second initial datum's physical L2 norm; arbitrary initial mismatch stays. -/
theorem solution_potential_spatialL2_le (v w : ℤ → H →L[ℂ] H)
    (hv : Exp014.RegularPotential v) (hw : Exp014.RegularPotential w)
    (hvHerm : Exp014.HermitianFourierPotential v)
    (hwHerm : Exp014.HermitianFourierPotential w)
    (a c : Exp014.FourierState H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ x, ‖Exp014.operatorPotential v x - Exp014.operatorPotential w x‖ ≤ δ)
    (b t : ℝ) (ht : 0 ≤ t) :
    Exp015.spatialL2 (fun x => Exp014.solution v a t x - Exp014.solution w c t x)
      b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => Exp014.synth a x - Exp014.synth c x) b (2 * Real.pi) +
        t * δ * Exp015.spatialL2 (Exp014.synth c) b (2 * Real.pi) := by
  have hregular := Exp015.classical_regular (Exp014.solution_classical w hw c)
  have hres := Exp015.pdeResidual_continuous
    (fun _ x => Exp014.operatorPotential v x) (Exp014.solution w c) hregular
    ((Exp014.operatorPotential_continuous v hv).comp continuous_snd)
  have hbudget : ∀ r ∈ Set.Icc 0 t,
      Exp015.spatialL2
        (Exp015.pdeResidual (fun _ x => Exp014.operatorPotential v x) (Exp014.solution w c) r)
        b (2 * Real.pi) ≤ δ * Exp015.spatialL2 (Exp014.synth c) b (2 * Real.pi) := by
    intro r _hr
    have he : Exp015.pdeResidual (fun _ x => Exp014.operatorPotential v x)
        (Exp014.solution w c) r =
        (fun x => (Exp014.operatorPotential w x - Exp014.operatorPotential v x)
          (Exp014.solution w c r x)) :=
      funext fun x => solution_pdeResidual_other_potential v w hw c r x
    rw [he]
    have hcu : Continuous (Exp014.solution w c r) :=
      continuous_iff_continuousAt.mpr fun x =>
        (Exp014.solution_space_hasDerivAt w c r x).continuousAt
    have hdrev : ∀ x, ‖Exp014.operatorPotential w x - Exp014.operatorPotential v x‖ ≤ δ := by
      intro x
      rw [norm_sub_rev]
      exact hd x
    have hb := spatialL2_operator_le
      (fun x => Exp014.operatorPotential w x - Exp014.operatorPotential v x)
      (Exp014.solution w c r)
      ((Exp014.operatorPotential_continuous w hw).sub
        (Exp014.operatorPotential_continuous v hv))
      hcu δ hδ hdrev
      b (2 * Real.pi) (by positivity)
    rw [solution_spatialL2_conserved w hw hwHerm c b r] at hb
    exact hb
  have hb := Exp015.residual_error_uniform_budget (Exp014.solution w c) (Exp014.solution v a)
    hregular (Exp014.solution_classical v hv a)
    (fun _ x => Exp014.operatorPotential_selfAdjoint v hvHerm x)
    (by positivity : 0 < 2 * Real.pi) hres b 0 t
    (δ * Exp015.spatialL2 (Exp014.synth c) b (2 * Real.pi)) ht hbudget
  rw [cps_spatialL2_sub_comm (Exp014.solution v a t) (Exp014.solution w c t)]
  calc
    _ ≤ Exp015.spatialL2 (fun x => Exp014.synth c x - Exp014.synth a x) b (2 * Real.pi) +
        t * (δ * Exp015.spatialL2 (Exp014.synth c) b (2 * Real.pi)) := by
      simpa only [Exp014.solution_zero, sub_zero] using hb
    _ = _ := by
      rw [cps_spatialL2_sub_comm (Exp014.synth c) (Exp014.synth a)]
      ring

#print axioms solution_pdeResidual_other_potential
#print axioms solution_spatialL2_conserved
#print axioms solution_potential_spatialL2_le

end NDEAEvolve.Exp016
