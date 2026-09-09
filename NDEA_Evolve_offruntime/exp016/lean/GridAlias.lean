import StencilFourier

/-! Exact aliases of arbitrary integer Fourier modes on the full odd grid.
The centered representative is unique, so the reconstructed aliased mode
preserves its pointwise amplitude even outside the principal frequency band.
-/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

/-- The DFT coefficient includes every congruent integer frequency. -/
theorem fourierCoefficient_modeLift_alias (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (r : Fin (2 * M + 1)) (u : E 2) :
    fourierCoefficient M h (modeLiftCLM (2 * M) h ell u) r =
      if ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r then u else 0 := by
  classical
  have hN : ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 * M + 1 ≠ 0 by omega)
  have hn (j : Fin (2 * M + 1)) :
      Exp011.nodeValue (2 * M) (modeLiftCLM (2 * M) h ell u) j =
        phase ((ell : ℝ) * ((j.val : ℝ) * h)) • u := by
    ext a
    rfl
  have hp (j : Fin (2 * M + 1)) :
      phase (-((oddFrequency M r : ℝ) * ((j.val : ℝ) * h))) *
          phase ((ell : ℝ) * ((j.val : ℝ) * h)) =
        phase (((ell - oddFrequency M r : ℤ) : ℝ) * ((j.val : ℝ) * h)) := by
    rw [← phase_add]
    congr 1
    push_cast
    ring
  unfold fourierCoefficient
  simp_rw [hn, smul_smul, hp]
  rw [← Finset.sum_smul]
  by_cases hd : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r
  · have hphase : phase (((ell - oddFrequency M r : ℤ) : ℝ) * h) = 1 :=
      (phase_mesh_eq_one_iff_dvd (2 * M) h hmesh _).mpr hd
    have hj (j : Fin (2 * M + 1)) :
        phase (((ell - oddFrequency M r : ℤ) : ℝ) * ((j.val : ℝ) * h)) = 1 := by
      calc
        _ = phase (((j.val : ℝ)) * (((ell - oddFrequency M r : ℤ) : ℝ) * h)) := by
          congr 1
          ring
        _ = phase (((ell - oddFrequency M r : ℤ) : ℝ) * h) ^ j.val := phase_nat_mul _ _
        _ = 1 := by rw [hphase, one_pow]
    simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hN, one_smul, if_pos hd]
  · rw [phase_sum_zero (2 * M) h hmesh _ hd, zero_smul, smul_zero, if_neg hd]

private theorem gridAlias_frequency_bound (M : ℕ) (r : Fin (2 * M + 1)) :
    |(oddFrequency M r : ℝ)| ≤ (M : ℝ) := by
  have hr : r.val ≤ 2 * M := Nat.le_of_lt_succ r.isLt
  have hrR : (r.val : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
  simp only [oddFrequency, Int.cast_sub, Int.cast_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem gridAlias_unique (M : ℕ) (ell : ℤ) (r s : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r)
    (hs : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M s) : r = s := by
  by_contra hrs
  apply band_difference_not_dvd M (2 * M) (oddFrequency M r) (oddFrequency M s)
    (gridAlias_frequency_bound M r) (gridAlias_frequency_bound M s) (by omega)
    (fun he => hrs (oddFrequency_injective M he))
  have hd := dvd_sub hr hs
  have he : (ell - oddFrequency M r) - (ell - oddFrequency M s) =
      oddFrequency M s - oddFrequency M r := by ring
  rw [he] at hd
  exact hd

/-- Every integer has exactly one representative in the centered full odd band. -/
theorem existsUnique_gridAlias (M : ℕ) (ell : ℤ) :
    ∃! r : Fin (2 * M + 1), ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r := by
  let N : ℤ := ((2 * M + 1 : ℕ) : ℤ)
  let j : ℤ := (ell + (M : ℤ)) % N
  have hN : 0 < N := by dsimp [N]; omega
  have hj0 : 0 ≤ j := Int.emod_nonneg _ hN.ne'
  have hjN : j < N := Int.emod_lt_of_pos _ hN
  let r : Fin (2 * M + 1) := ⟨j.toNat, by dsimp [N] at hjN; omega⟩
  have hj : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  have hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r := by
    refine ⟨(ell + (M : ℤ)) / N, ?_⟩
    change ell - ((j.toNat : ℤ) - (M : ℤ)) = N * ((ell + (M : ℤ)) / N)
    rw [hj]
    have he := Int.mul_ediv_add_emod (ell + (M : ℤ)) N
    dsimp only [j]
    omega
  exact ⟨r, hr, fun s hs => gridAlias_unique M ell s r hs hr⟩

theorem fourierReconstruction_modeLift_alias (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (u : E 2) (x : ℝ) :
    fourierReconstruction M h (modeLiftCLM (2 * M) h ell u) x =
      fourierSynthesis M (fun r =>
        if ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r then u else 0) x := by
  simp only [fourierReconstruction, fourierSynthesis, fourierCoefficient_modeLift_alias M h hmesh]

/-- Reconstruction is the single centered representative, including aliased input modes. -/
theorem fourierReconstruction_modeLift_alias_frequency (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (r : Fin (2 * M + 1))
    (hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r) (u : E 2) (x : ℝ) :
    fourierReconstruction M h (modeLiftCLM (2 * M) h ell u) x =
      phase ((oddFrequency M r : ℝ) * x) • u := by
  classical
  rw [fourierReconstruction_modeLift_alias M h hmesh, fourierSynthesis]
  have hc (s : Fin (2 * M + 1)) :
      ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M s ↔ s = r :=
    ⟨fun hs => gridAlias_unique M ell s r hs hr, fun he => he.symm ▸ hr⟩
  simp_rw [hc]
  simp

/-- Aliasing changes the represented frequency but preserves pointwise amplitude. -/
theorem norm_fourierReconstruction_modeLift (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (u : E 2) (x : ℝ) :
    ‖fourierReconstruction M h (modeLiftCLM (2 * M) h ell u) x‖ = ‖u‖ := by
  obtain ⟨r, hr, _⟩ := existsUnique_gridAlias M ell
  rw [fourierReconstruction_modeLift_alias_frequency M h hmesh ell r hr]
  simp only [norm_smul, phase_norm, one_mul]

/-- Every integer mode within the principal band is reconstructed exactly. -/
theorem fourierReconstruction_phase_of_memBand (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (hell : |(ell : ℝ)| ≤ (M : ℝ)) (u : E 2) (x : ℝ) :
    fourierReconstruction M h (modeLiftCLM (2 * M) h ell u) x =
      phase ((ell : ℝ) * x) • u := by
  have heZ : |ell| ≤ (M : ℤ) := by exact_mod_cast hell
  have hb := abs_le.mp heZ
  have hj0 : 0 ≤ ell + (M : ℤ) := by omega
  let r : Fin (2 * M + 1) := ⟨(ell + (M : ℤ)).toNat, by omega⟩
  have hfreq : oddFrequency M r = ell := by
    change ((ell + (M : ℤ)).toNat : ℤ) - (M : ℤ) = ell
    rw [Int.toNat_of_nonneg hj0]
    omega
  have hr : ((2 * M + 1 : ℕ) : ℤ) ∣ ell - oddFrequency M r := by
    rw [hfreq, sub_self]
    exact dvd_zero _
  simpa only [hfreq] using fourierReconstruction_modeLift_alias_frequency M h hmesh ell r hr u x

theorem fourierReconstruction_modeLift_spatialL2 (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (ell : ℤ) (u : E 2) (b : ℝ) :
    Exp015.spatialL2 (fourierReconstruction M h (modeLiftCLM (2 * M) h ell u))
      b (2 * Real.pi) = Real.sqrt (2 * Real.pi) * ‖u‖ := by
  rw [fourierReconstruction_spatialL2 M h hmesh, modeLiftCLM_apply]
  have hh : 0 ≤ h := by
    have hN : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by positivity
    nlinarith [Real.pi_pos]
  exact modeLift_weighted_norm (2 * M) h ell hh hmesh u

#print axioms fourierCoefficient_modeLift_alias
#print axioms existsUnique_gridAlias
#print axioms fourierReconstruction_modeLift_alias
#print axioms fourierReconstruction_modeLift_alias_frequency
#print axioms norm_fourierReconstruction_modeLift
#print axioms fourierReconstruction_phase_of_memBand
#print axioms fourierReconstruction_modeLift_spatialL2
end NDEAEvolve.Exp016
