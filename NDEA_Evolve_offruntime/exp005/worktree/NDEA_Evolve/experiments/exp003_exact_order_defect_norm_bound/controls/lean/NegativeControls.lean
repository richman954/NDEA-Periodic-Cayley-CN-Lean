import NDEAEvolve.Experiments.Exp003.ExactOrderDefectNormBound
import NDEAEvolve.Experiments.Exp002.AdversarialWitnesses

noncomputable section
open Matrix NDEAEvolve.Exp002
open NDEAEvolve.Exp002.AdversarialWitnesses
namespace NDEAEvolve.Exp003.Step2Controls

abbrev Op2 := E 2 →L[ℂ] E 2

def Khat : Op2 := operatorOf pauliX * operatorOf pauliZ -
  operatorOf pauliZ * operatorOf pauliX

theorem Khat_ne_zero : Khat ≠ 0 := by
  intro h
  change
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toRingEquiv pauliX *
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toRingEquiv pauliZ -
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toRingEquiv pauliZ *
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toRingEquiv pauliX = 0 at h
  have hm : NDEAEvolve.Exp002.commutator pauliX pauliZ = 0 := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)).toRingEquiv.injective
    simpa only [NDEAEvolve.Exp002.commutator, map_sub, map_mul, map_zero] using h
  exact pauli_generators_do_not_commute
    ((NDEAEvolve.Exp002.commutator_eq_zero_iff_commute pauliX pauliZ).mp hm)

theorem Khat_norm_pos : 0 < ‖Khat‖ := norm_pos_iff.mpr Khat_ne_zero

/-- Negative control A: omitting the absolute value makes the right side
strictly negative at `α = -1`, `β = 1` for noncommuting Hermitian generators. -/
theorem missing_absolute_value_false :
    ¬ ‖Chat pauliX (-1) * Chat pauliZ 1 -
          Chat pauliZ 1 * Chat pauliX (-1)‖ ≤
        4 * (-1 : ℝ) * 1 * ‖Khat‖ := by
  intro h
  have hn := norm_nonneg
    (Chat pauliX (-1) * Chat pauliZ 1 - Chat pauliZ 1 * Chat pauliX (-1))
  nlinarith [Khat_norm_pos]

def halfRX : Mat2 :=
  !![(4 : ℂ) / 5, -((2 : ℂ) / 5) * Complex.I;
     -((2 : ℂ) / 5) * Complex.I, (4 : ℂ) / 5]

def halfRZ : Mat2 :=
  !![((4 : ℂ) - 2 * Complex.I) / 5, 0;
     0, ((4 : ℂ) + 2 * Complex.I) / 5]

theorem halfRX_eq_cayleyR : halfRX = cayleyR (1 / 2) pauliX := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyD, skewPart, cscalar, pauliX, halfRX,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem halfRZ_eq_cayleyR : halfRZ = cayleyR (1 / 2) pauliZ := by
  symm
  unfold cayleyR
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyD, skewPart, cscalar, pauliZ, halfRZ,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num

theorem half_cayleyX_eq : cayley (1 / 2) pauliX = pauliUX := by
  unfold cayley
  rw [← halfRX_eq_cayleyR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyN, skewPart, cscalar, pauliX, halfRX, pauliUX,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num

def halfUZ : Mat2 :=
  !![((3 : ℂ) - 4 * Complex.I) / 5, 0;
     0, ((3 : ℂ) + 4 * Complex.I) / 5]

theorem half_cayleyZ_eq : cayley (1 / 2) pauliZ = halfUZ := by
  unfold cayley
  rw [← halfRZ_eq_cayleyR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cayleyN, skewPart, cscalar, pauliZ, halfRZ, halfUZ,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I] <;> ring
  all_goals rw [Complex.I_sq] <;> norm_num <;> ring

theorem half_cayley_commutator_hat :
    Chat pauliX (1 / 2) * Chat pauliZ (1 / 2) -
        Chat pauliZ (1 / 2) * Chat pauliX (1 / 2) =
      ((-16 : ℂ) / 25) • Khat := by
  have hm : pauliUX * halfUZ - halfUZ * pauliUX =
      ((-16 : ℂ) / 25) • (pauliX * pauliZ - pauliZ * pauliX) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliUX, halfUZ, pauliX, pauliZ, Matrix.mul_apply,
        Fin.sum_univ_two, Complex.I_mul_I] <;> ring
    all_goals rw [Complex.I_sq] <;> norm_num
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (cayley (1 / 2) pauliX) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (cayley (1 / 2) pauliZ) -
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (cayley (1 / 2) pauliZ) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (cayley (1 / 2) pauliX) = _
  rw [half_cayleyX_eq, half_cayleyZ_eq]
  simpa only [Khat, operatorOf, map_sub, map_mul, map_smul] using
    congrArg
      (fun M : Mat2 => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) M) hm

/-- Negative control B: coefficient `1` in place of `4` fails already for
the Pauli generators at equal half steps. -/
theorem missing_factor_four_false :
    ¬ ‖Chat pauliX (1 / 2) * Chat pauliZ (1 / 2) -
          Chat pauliZ (1 / 2) * Chat pauliX (1 / 2)‖ ≤
        |(1 / 2 : ℝ) * (1 / 2 : ℝ)| * ‖Khat‖ := by
  rw [half_cayley_commutator_hat, norm_smul]
  have hs : ‖((-16 : ℂ) / 25)‖ = (16 : ℝ) / 25 := by norm_num
  rw [hs]
  have habs : |(1 / 2 : ℝ) * (1 / 2 : ℝ)| = 1 / 4 := by norm_num
  rw [habs]
  intro h
  nlinarith [Khat_norm_pos]

/-- Audit-strength packaging of negative control A, including Hermiticity. -/
theorem missing_absolute_value_counterexample :
    pauliX.IsHermitian ∧ pauliZ.IsHermitian ∧
      ¬ ‖Chat pauliX (-1) * Chat pauliZ 1 -
            Chat pauliZ 1 * Chat pauliX (-1)‖ ≤
          4 * (-1 : ℝ) * 1 * ‖Khat‖ :=
  ⟨pauliX_hermitian, pauliZ_hermitian, missing_absolute_value_false⟩

/-- Audit-strength packaging of negative control B, including Hermiticity. -/
theorem missing_factor_four_counterexample :
    pauliX.IsHermitian ∧ pauliZ.IsHermitian ∧
      ¬ ‖Chat pauliX (1 / 2) * Chat pauliZ (1 / 2) -
            Chat pauliZ (1 / 2) * Chat pauliX (1 / 2)‖ ≤
          |(1 / 2 : ℝ) * (1 / 2 : ℝ)| * ‖Khat‖ :=
  ⟨pauliX_hermitian, pauliZ_hermitian, missing_factor_four_false⟩

end NDEAEvolve.Exp003.Step2Controls

#check NDEAEvolve.Exp003.Step2Controls.missing_absolute_value_false
#check NDEAEvolve.Exp003.Step2Controls.missing_factor_four_false
#check NDEAEvolve.Exp003.Step2Controls.missing_absolute_value_counterexample
#check NDEAEvolve.Exp003.Step2Controls.missing_factor_four_counterexample
#print axioms NDEAEvolve.Exp003.Step2Controls.missing_absolute_value_counterexample
#print axioms NDEAEvolve.Exp003.Step2Controls.missing_factor_four_counterexample
