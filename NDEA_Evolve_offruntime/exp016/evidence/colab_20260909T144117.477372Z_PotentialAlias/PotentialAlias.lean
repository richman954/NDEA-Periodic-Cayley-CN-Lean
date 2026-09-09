import GridAlias
import SampledCayleyCertificate

/-! Exact sampling aliases for the actual Exp014 Fourier potential.
The potential acts on the actual grid state. Absolute summability justifies
the operator-series interchange; no Hermitian or residual-smallness premise
is needed. The final formula enumerates every alias by its integer shift.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

private theorem pa_modeLift_norm (n : ℕ) (h : ℝ) (m : ℤ) (u : E 2) :
    ‖modeLiftCLM n h m u‖ = Real.sqrt ((n + 1 : ℕ) : ℝ) * ‖u‖ := by
  rw [modeLiftCLM_apply, ← Real.sqrt_sq (norm_nonneg (modeLift n h m u)),
    modeLift_norm_sq, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg u)]

private theorem pa_character_phase (ell m : ℤ) (x : ℝ) :
    Exp014.character x ell * phase ((m : ℝ) * x) =
      phase (((ell + m : ℤ) : ℝ) * x) := by
  have he : Exp014.character x ell = phase ((ell : ℝ) * x) := by
    unfold Exp014.character phase
    congr 1
    push_cast
    ring
  rw [he, ← phase_add]
  congr 1
  push_cast
  ring

private theorem pa_node_modeLift (n : ℕ) (h : ℝ) (m : ℤ) (u : E 2)
    (i : Fin (n + 1)) :
    Exp011.nodeValue n (modeLiftCLM n h m u) i =
      phase ((m : ℝ) * ((i.val : ℝ) * h)) • u := by
  ext a
  rfl

/-- Absolute potential summability controls the full grid-valued mode series. -/
theorem potential_modeLift_terms_summable (n : ℕ) (h : ℝ) (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) :
    Summable (fun ell : ℤ => modeLiftCLM n h (ell + m) (v ell u)) := by
  apply (((Exp014.regularPotential_absolute v hv).mul_right ‖u‖).mul_left
    (Real.sqrt ((n + 1 : ℕ) : ℝ))).of_norm_bounded
  intro ell
  rw [pa_modeLift_norm]
  exact mul_le_mul_of_nonneg_left ((v ell).le_opNorm u) (Real.sqrt_nonneg _)

/-- Applying the sampled potential to one arbitrary integer mode produces
the absolutely convergent series of shifted modes, with the original v ell. -/
theorem sampledPotential_on_modeLift (n : ℕ) (h : ℝ) (m : ℤ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) :
    op (sampledBlock n h (operatorPotentialMatrix v)) (modeLiftCLM n h m u) =
      ∑' ell : ℤ, modeLiftCLM n h (ell + m) (v ell u) := by
  have hs := potential_modeLift_terms_summable n h m v hv u
  have he (i : Fin (n + 1)) :
      Exp011.nodeValue n
        (op (sampledBlock n h (operatorPotentialMatrix v)) (modeLiftCLM n h m u)) i =
        Exp011.nodeValue n (∑' ell : ℤ, modeLiftCLM n h (ell + m) (v ell u)) i := by
    rw [sampled_operatorPotential_nodeValue, pa_node_modeLift,
      Exp014.operatorPotential_apply v hv]
    have hr := (nodeValueCLM n i).map_tsum hs
    simp only [nodeValueCLM_apply, pa_node_modeLift] at hr
    rw [hr]
    apply tsum_congr
    intro ell
    rw [map_smul, smul_smul, pa_character_phase]
  ext p
  rcases p with ⟨i, a⟩
  exact congrArg (fun z : E 2 => z a) (he i)

/-- Each output DFT coefficient retains exactly the congruent input/potential
mode pairs. This intermediate form preserves the original potential index. -/
theorem sampledPotential_fourierCoefficient_filtered (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (r : Fin (2 * M + 1)) :
    fourierCoefficient M h (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y) r =
      ∑ m : Fin (2 * M + 1), ∑' ell : ℤ,
        if ((2 * M + 1 : ℕ) : ℤ) ∣ ell + oddFrequency M m - oddFrequency M r
        then v ell (fourierCoefficient M h y m) else 0 := by
  classical
  rw [← fourierCoefficientCLM_apply M h r]
  calc
    _ = fourierCoefficientCLM M h r (op (sampledBlock (2 * M) h
        (operatorPotentialMatrix v)) (∑ m : Fin (2 * M + 1),
          modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m))) :=
      congrArg (fun z => fourierCoefficientCLM M h r
        (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) z))
          (gridState_eq_modeLift_sum M h hmesh y)
    _ = ∑ m : Fin (2 * M + 1), fourierCoefficientCLM M h r
        (op (sampledBlock (2 * M) h (operatorPotentialMatrix v))
          (modeLiftCLM (2 * M) h (oddFrequency M m) (fourierCoefficient M h y m))) := by
      simp only [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [sampledPotential_on_modeLift (2 * M) h (oddFrequency M m) v hv]
      rw [(fourierCoefficientCLM M h r).map_tsum
        (potential_modeLift_terms_summable (2 * M) h (oddFrequency M m) v hv _)]
      apply tsum_congr
      intro ell
      simp only [fourierCoefficientCLM_apply,
        fourierCoefficient_modeLift_alias M h hmesh]

private theorem pa_progression_injective (N r m : ℤ) (hN : N ≠ 0) :
    Function.Injective (fun q : ℤ => r - m + q * N) := by
  intro q p hp
  exact mul_right_cancel₀ hN (add_left_cancel hp)

private theorem pa_filtered_tsum (N r m : ℤ) (hN : N ≠ 0) (f : ℤ → E 2) :
    (∑' ell : ℤ, if N ∣ ell + m - r then f ell else 0) =
      ∑' q : ℤ, f (r - m + q * N) := by
  classical
  let F : ℤ → E 2 := fun ell => if N ∣ ell + m - r then f ell else 0
  have hs : Function.support F ⊆ Set.range (fun q : ℤ => r - m + q * N) := by
    intro ell hell
    have hd : N ∣ ell + m - r := by
      by_contra hn
      exact hell (by simp only [F, if_neg hn])
    rcases hd with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [mul_comm N q] at hq
    change r - m + q * N = ell
    omega
  have he := (pa_progression_injective N r m hN).tsum_eq hs
  have hd (q : ℤ) : N ∣ (r - m + q * N) + m - r := by
    refine ⟨q, ?_⟩
    ring
  calc
    _ = ∑' q : ℤ, F (r - m + q * N) := he.symm
    _ = _ := tsum_congr fun q => if_pos (hd q)

/-- Every arithmetic progression alias series is summable; its `tsum` is an
ordinary absolutely convergent series, including all negative and zero shifts. -/
theorem potential_alias_progression_summable (N r m : ℤ) (hN : N ≠ 0)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) (u : E 2) :
    Summable (fun q : ℤ => v (r - m + q * N) u) := by
  have hs : Summable (fun ell : ℤ => v ell u) :=
    ((Exp014.regularPotential_absolute v hv).mul_right ‖u‖).of_norm_bounded
      (fun ell => (v ell).le_opNorm u)
  exact hs.comp_injective (pa_progression_injective N r m hN)

/-- The actual sampled product coefficient is the complete integer-shift
alias convolution. No band truncation, Hermitian condition or decay estimate
is substituted for the original regular potential and arbitrary grid state. -/
theorem sampledPotential_fourierCoefficient_alias (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (y : Vec (Grid (2 * M))) (r : Fin (2 * M + 1)) :
    fourierCoefficient M h (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) y) r =
      ∑ m : Fin (2 * M + 1), ∑' q : ℤ,
        v (oddFrequency M r - oddFrequency M m + q * ((2 * M + 1 : ℕ) : ℤ))
          (fourierCoefficient M h y m) := by
  rw [sampledPotential_fourierCoefficient_filtered M h hmesh v hv]
  apply Finset.sum_congr rfl
  intro m _
  apply pa_filtered_tsum
  exact_mod_cast (show 2 * M + 1 ≠ 0 by omega)

#print axioms potential_modeLift_terms_summable
#print axioms sampledPotential_on_modeLift
#print axioms sampledPotential_fourierCoefficient_filtered
#print axioms potential_alias_progression_summable
#print axioms sampledPotential_fourierCoefficient_alias
end NDEAEvolve.Exp016
