import ResidualField

/-! Exact regularity and residual algebra for a globally affine time extension
of two periodic spatial profiles. No estimate of the residual, stitching across
time slabs, or numerical convergence rate is assumed or concluded here. -/
noncomputable section
namespace NDEAEvolve.Exp016

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Explicit spatial regularity sufficient for the accepted classical residual API. -/
structure IsRegularPeriodicProfile (L : ℝ) (a : ℝ → H) : Prop where
  differentiable : Differentiable ℝ a
  second_differentiable : Differentiable ℝ (deriv a)
  continuous_second_derivative : Continuous (deriv (deriv a))
  periodic : Function.Periodic a L

def affineTimeWeight (t₀ k t : ℝ) : ℝ := (t - t₀) / k

def affineProfile (a b : ℝ → H) (t₀ k t x : ℝ) : H :=
  a x + affineTimeWeight t₀ k t • (b x - a x)

theorem affineProfile_left (a b : ℝ → H) (t₀ k x : ℝ) :
    affineProfile a b t₀ k t₀ x = a x := by
  simp [affineProfile, affineTimeWeight]

theorem affineProfile_right (a b : ℝ → H) (t₀ k x : ℝ) (hk : k ≠ 0) :
    affineProfile a b t₀ k (t₀ + k) x = b x := by
  simp [affineProfile, affineTimeWeight, hk]

theorem affineTimeWeight_hasDerivAt (t₀ k t : ℝ) :
    HasDerivAt (affineTimeWeight t₀ k) k⁻¹ t := by
  change HasDerivAt (fun s : ℝ => (s - t₀) / k) k⁻¹ t
  simpa only [one_div, id_eq] using!
    ((hasDerivAt_id t).sub_const t₀).div_const k

theorem affineProfile_time_hasDerivAt (a b : ℝ → H) (t₀ k t x : ℝ) :
    HasDerivAt (fun s => affineProfile a b t₀ k s x) (k⁻¹ • (b x - a x)) t := by
  exact ((affineTimeWeight_hasDerivAt t₀ k t).smul_const (b x - a x)).const_add (a x)

theorem affineProfile_time_derivative (a b : ℝ → H) (t₀ k t x : ℝ) :
    deriv (fun s => affineProfile a b t₀ k s x) t = k⁻¹ • (b x - a x) :=
  (affineProfile_time_hasDerivAt a b t₀ k t x).deriv

theorem affineProfile_space_hasDerivAt (a b : ℝ → H)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (t₀ k t x : ℝ) :
    HasDerivAt (affineProfile a b t₀ k t)
      (deriv a x + affineTimeWeight t₀ k t • (deriv b x - deriv a x)) x := by
  exact (ha x).hasDerivAt.add
    (((hb x).hasDerivAt.sub (ha x).hasDerivAt).const_smul (affineTimeWeight t₀ k t))

theorem affineProfile_space_derivative (a b : ℝ → H)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (t₀ k t x : ℝ) :
    deriv (affineProfile a b t₀ k t) x =
      deriv a x + affineTimeWeight t₀ k t • (deriv b x - deriv a x) :=
  (affineProfile_space_hasDerivAt a b ha hb t₀ k t x).deriv

theorem affineProfile_second_hasDerivAt (a b : ℝ → H)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (ha₂ : Differentiable ℝ (deriv a)) (hb₂ : Differentiable ℝ (deriv b))
    (t₀ k t x : ℝ) :
    HasDerivAt (deriv (affineProfile a b t₀ k t))
      (deriv (deriv a) x + affineTimeWeight t₀ k t •
        (deriv (deriv b) x - deriv (deriv a) x)) x := by
  have he : deriv (affineProfile a b t₀ k t) =
      affineProfile (deriv a) (deriv b) t₀ k t :=
    funext (affineProfile_space_derivative a b ha hb t₀ k t)
  rw [he]
  exact affineProfile_space_hasDerivAt (deriv a) (deriv b) ha₂ hb₂ t₀ k t x

theorem affineProfile_second_derivative (a b : ℝ → H)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (ha₂ : Differentiable ℝ (deriv a)) (hb₂ : Differentiable ℝ (deriv b))
    (t₀ k t x : ℝ) :
    deriv (deriv (affineProfile a b t₀ k t)) x =
      deriv (deriv a) x + affineTimeWeight t₀ k t •
        (deriv (deriv b) x - deriv (deriv a) x) :=
  (affineProfile_second_hasDerivAt a b ha hb ha₂ hb₂ t₀ k t x).deriv

theorem affineProfile_continuous (a b : ℝ → H)
    (ha : Continuous a) (hb : Continuous b) (t₀ k : ℝ) :
    Continuous (fun p : ℝ × ℝ => affineProfile a b t₀ k p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => affineTimeWeight t₀ k p.1) :=
    (continuous_fst.sub continuous_const).div_const k
  exact (ha.comp continuous_snd).add
    (hc.smul ((hb.comp continuous_snd).sub (ha.comp continuous_snd)))

theorem affineProfile_periodic (a b : ℝ → H) {L : ℝ}
    (ha : Function.Periodic a L) (hb : Function.Periodic b L) (t₀ k t : ℝ) :
    Function.Periodic (affineProfile a b t₀ k t) L := by
  intro x
  simp only [affineProfile, ha x, hb x]

theorem affineProfile_regular (a b : ℝ → H) {L : ℝ}
    (ha : IsRegularPeriodicProfile L a) (hb : IsRegularPeriodicProfile L b)
    (t₀ k : ℝ) : Exp015.IsRegularPeriodicField L (affineProfile a b t₀ k) where
  time_differentiable t x := (affineProfile_time_hasDerivAt a b t₀ k t x).differentiableAt
  space_differentiable t x :=
    (affineProfile_space_hasDerivAt a b ha.differentiable hb.differentiable t₀ k t x).differentiableAt
  second_space_differentiable t x :=
    (affineProfile_second_hasDerivAt a b ha.differentiable hb.differentiable
      ha.second_differentiable hb.second_differentiable t₀ k t x).differentiableAt
  continuous_solution :=
    affineProfile_continuous a b ha.differentiable.continuous hb.differentiable.continuous t₀ k
  continuous_time_derivative := by
    simp only [affineProfile_time_derivative]
    exact ((hb.differentiable.continuous.comp continuous_snd).sub
      (ha.differentiable.continuous.comp continuous_snd)).const_smul k⁻¹
  continuous_space_derivative := by
    simp only [affineProfile_space_derivative a b ha.differentiable hb.differentiable]
    exact affineProfile_continuous (deriv a) (deriv b)
      ha.second_differentiable.continuous hb.second_differentiable.continuous t₀ k
  continuous_second_derivative := by
    simp only [affineProfile_second_derivative a b ha.differentiable hb.differentiable
      ha.second_differentiable hb.second_differentiable]
    exact affineProfile_continuous (deriv (deriv a)) (deriv (deriv b))
      ha.continuous_second_derivative hb.continuous_second_derivative t₀ k
  periodic := affineProfile_periodic a b ha.periodic hb.periodic t₀ k

/-- The computed derivative expression is the actual accepted PDE residual. -/
theorem affineProfile_pdeResidual (a b : ℝ → H)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (ha₂ : Differentiable ℝ (deriv a)) (hb₂ : Differentiable ℝ (deriv b))
    (V : ℝ → ℝ → H →L[ℂ] H) (t₀ k t x : ℝ) :
    Exp015.pdeResidual V (affineProfile a b t₀ k) t x =
      Complex.I • (k⁻¹ • (b x - a x)) +
        (deriv (deriv a) x + affineTimeWeight t₀ k t •
          (deriv (deriv b) x - deriv (deriv a) x)) -
        V t x (a x + affineTimeWeight t₀ k t • (b x - a x)) := by
  rw [Exp015.pdeResidual, affineProfile_time_derivative,
    affineProfile_second_derivative a b ha hb ha₂ hb₂]
  rfl

/-- A linear spatial synthesis commutes with the actual affine state formula.
The state space needs only its real module structure for this algebraic fact. -/
theorem synthesis_affineProfile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J : E →ₗ[ℝ] (ℝ → H)) (q₀ q₁ : E) (t₀ k t x : ℝ) :
    J (q₀ + affineTimeWeight t₀ k t • (q₁ - q₀)) x =
      affineProfile (J q₀) (J q₁) t₀ k t x := by
  simp only [map_add, map_smul, map_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    affineProfile]

end NDEAEvolve.Exp016
