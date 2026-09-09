import TargetBinding
import SampledPotential

/-! A nonzero spinor and genuinely variable scalar matrix potential exercise
the actual ordered grid stages and the independently specified reconstruction.
The single-node spatial discrepancy is nonzero; this is a certificate control,
not a spatial convergence or order claim. -/
noncomputable section
open scoped BigOperators Matrix
open Set
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016.OneNodeCosine

def spinor : E 2 := WithLp.toLp 2 ![(1 : ℂ), 0]

theorem spinor_ne_zero : spinor ≠ 0 := by
  intro h
  have he := congrArg (fun z : E 2 => z 0) h
  norm_num [spinor] at he

def coefficients (m : ℤ) : E 2 →L[ℂ] E 2 :=
  if m = 1 ∨ m = -1 then ContinuousLinearMap.id ℂ (E 2) else 0

private theorem coefficients_offsupport (m : ℤ)
    (hm : m ∉ ({1, -1} : Finset ℤ)) : coefficients m = 0 := by
  have hn : m ≠ 1 ∧ m ≠ -1 := by simpa using hm
  simp [coefficients, hn.1, hn.2]

theorem coefficients_regular : Exp014.RegularPotential coefficients := by
  apply (hasSum_sum_of_ne_finset_zero (s := ({1, -1} : Finset ℤ))
    (f := fun m : ℤ => Exp014.weight m * ‖coefficients m‖) ?_).summable
  intro m hm
  simp only [coefficients_offsupport m hm, norm_zero, mul_zero]

theorem coefficients_hermitian : Exp014.HermitianFourierPotential coefficients := by
  intro m
  have hi : star (ContinuousLinearMap.id ℂ (E 2)) = ContinuousLinearMap.id ℂ (E 2) := by
    change star (1 : E 2 →L[ℂ] E 2) = 1
    simp
  have he : (-m = 1 ∨ -m = -1) ↔ (m = 1 ∨ m = -1) := by omega
  by_cases hm : m = 1 ∨ m = -1
  · simp only [coefficients, if_pos hm, if_pos (he.mpr hm), hi]
  · simp only [coefficients, if_neg hm, if_neg (not_congr he |>.mpr hm), star_zero]

private theorem character_pair (x : ℝ) :
    Exp014.character x 1 + Exp014.character x (-1) = ((2 * Real.cos x : ℝ) : ℂ) := by
  simpa [Exp014.character, Complex.ofReal_cos, mul_comm] using
    (Complex.two_cos (x : ℂ)).symm

theorem potential_apply (x : ℝ) (z : E 2) :
    Exp014.operatorPotential coefficients x z = ((2 * Real.cos x : ℝ) : ℂ) • z := by
  have hp : Exp014.operatorPotential coefficients x z =
      Exp014.character x 1 • z + Exp014.character x (-1) • z := by
    rw [Exp014.operatorPotential_apply coefficients coefficients_regular,
      tsum_eq_sum (s := ({1, -1} : Finset ℤ))]
    · norm_num [coefficients]
    · intro m hm
      simp only [coefficients_offsupport m hm, _root_.zero_apply, smul_zero]
  rw [hp, ← add_smul, character_pair]

def matrixPotential (x : ℝ) : Mat 2 := ((2 * Real.cos x : ℝ) : ℂ) • (1 : Mat 2)

theorem matrixPotential_hermitian (x : ℝ) : (matrixPotential x).IsHermitian := by
  change (matrixPotential x).conjTranspose = matrixPotential x
  simp only [matrixPotential, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

theorem potential_matches_matrix (x : ℝ) :
    Exp014.operatorPotential coefficients x = operatorOf (matrixPotential x) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [potential_apply]
  simp [matrixPotential, operatorOf, map_smul, map_one]

theorem potential_nonconstant :
    Exp014.operatorPotential coefficients 0 ≠ Exp014.operatorPotential coefficients Real.pi := by
  intro h
  have he := congrArg (fun V : E 2 →L[ℂ] E 2 => (V spinor) 0) h
  simp [potential_apply, spinor] at he
  norm_num at he

def initialCoefficients (m : ℤ) : E 2 := if m = 0 then spinor else 0

private theorem initialCoefficients_regular :
    Summable (fun m : ℤ => Exp014.weight m * ‖initialCoefficients m‖) := by
  have he : (fun m : ℤ => Exp014.weight m * ‖initialCoefficients m‖) =
      (fun m : ℤ => if m = 0 then Exp014.weight 0 * ‖spinor‖ else 0) := by
    funext m
    by_cases hm : m = 0 <;> simp [initialCoefficients, hm]
  rw [he]
  exact (hasSum_ite_eq 0 _).summable

def initialState : Exp014.FourierState (E 2) :=
  Exp014.ofCoefficients initialCoefficients initialCoefficients_regular

theorem reference_initial (x : ℝ) : Exp014.solution coefficients initialState 0 x = spinor := by
  rw [Exp014.solution_zero, Exp014.synth_eq_tsum]
  simp only [initialState, Exp014.coefficient_ofCoefficients]
  rw [tsum_eq_single 0]
  · simp [initialCoefficients, Exp014.character]
  · intro m hm
    simp [initialCoefficients, hm]

def gridInitial : Vec (Grid 0) := WithLp.toLp 2 (fun p => spinor p.2)
def mesh : ℝ := 2 * Real.pi
def A : Matrix (Grid 0) (Grid 0) ℂ := sampledSplitA 0 mesh
def B : Matrix (Grid 0) (Grid 0) ℂ := sampledSplitB 0 mesh matrixPotential

theorem A_hermitian : A.IsHermitian := sampledSplitA_isHermitian 0 mesh
theorem B_hermitian : B.IsHermitian :=
  sampledSplitB_isHermitian 0 mesh matrixPotential matrixPotential_hermitian

theorem gridInitial_ne_zero : gridInitial ≠ 0 := by
  intro h
  have he := congrArg (fun y : Vec (Grid 0) => y (0, 0)) h
  norm_num [gridInitial, spinor] at he

private theorem reconstruction_one_node (h x : ℝ) (y : Vec (Grid 0)) :
    fourierReconstruction 0 h y x = Exp011.nodeValue 0 y 0 := by
  simp [fourierReconstruction, fourierSynthesis, fourierCoefficient, oddFrequency, phase]

theorem reconstruction_initial (x : ℝ) :
    IndependentTarget.rawFourier 0 mesh gridInitial x = spinor := by
  rw [← fourierReconstruction_eq_independentTarget, reconstruction_one_node]
  rfl

private theorem generator_node (y : Vec (Grid 0)) :
    Exp011.nodeValue 0 ((op A + op B) y) 0 = (2 : ℂ) • Exp011.nodeValue 0 y 0 := by
  have hn : PeriodicGrid.next (0 : Fin 1) = 0 := by apply Fin.ext; omega
  have hp : PeriodicGrid.prev (0 : Fin 1) = 0 := by apply Fin.ext; omega
  ext a
  change op A y (0, a) + op B y (0, a) = 2 * y (0, a)
  rw [A, sampledSplitA, hamiltonian_apply_stencil, hn, hp,
    B, sampledSplitB, sampledBlock_apply]
  have hz : 2*y (0, a) - y (0, a) - y (0, a) = 0 := by ring
  simp only [hz, zero_div, zero_add]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, matrixPotential, Real.cos_zero,
    mul_one, Complex.ofReal_ofNat, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib]
  have hs : (∑ b : Fin 2, (2 * (1 : Mat 2) a b) * y (0, b)) = 2 * y (0, a) := by
    simp [Matrix.one_apply, mul_assoc, ← Finset.mul_sum]
  rw [hs]
  abel

theorem spatial_defect (x : ℝ) (y : Vec (Grid 0)) :
    (fourierRegularSynthesis 0 mesh).spatialDefect (op A + op B)
      (Exp014.operatorPotential coefficients) x y =
        ((2 - 2 * Real.cos x : ℝ) : ℂ) • Exp011.nodeValue 0 y 0 := by
  have hd : (fourierRegularSynthesis 0 mesh).dxx x y = 0 := by
    simp [fourierRegularSynthesis, fourierDxx, oddFrequency]
  simp only [RegularSynthesis.spatialDefect, _root_.sub_apply,
    _root_.add_apply, ContinuousLinearMap.comp_apply, hd, add_zero,
    fourierRegularSynthesis_eval, reconstruction_one_node, potential_apply]
  change Exp011.nodeValue 0 ((op A + op B) y) 0 -
    ((2 * Real.cos x : ℝ) : ℂ) • Exp011.nodeValue 0 y 0 = _
  rw [generator_node, ← sub_smul]
  norm_cast

theorem spatial_defect_at_pi :
    (fourierRegularSynthesis 0 mesh).spatialDefect (op A + op B)
      (Exp014.operatorPotential coefficients) Real.pi gridInitial = (4 : ℂ) • spinor := by
  rw [spatial_defect]
  norm_num [gridInitial, Exp011.nodeValue]

theorem spatial_defect_nonzero :
    (fourierRegularSynthesis 0 mesh).spatialDefect (op A + op B)
      (Exp014.operatorPotential coefficients) Real.pi gridInitial ≠ 0 := by
  rw [spatial_defect_at_pi]
  exact smul_ne_zero (by norm_num) spinor_ne_zero

/-- The actual A-half/B-full/A-half stages, the raw quadratic DFT target and
the nonzero Exp014 solution satisfy a derived partial-slab certificate. -/
theorem actual_slab_certificate (b k t : ℝ) (hk : 0 < k) (ht : t ∈ Icc 0 k) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.actualCayleyFourierSlab 0 mesh A B gridInitial 0 k t x -
        Exp014.solution coefficients initialState t x) b (2 * Real.pi) ≤
      t * actualFourierResidualBudget 0 mesh A B
        (Exp014.operatorPotential coefficients) gridInitial b k := by
  have he := independentTarget_variable_potential_slab_error 0 mesh
    (by simp [mesh]) A B A_hermitian B_hermitian coefficients coefficients_regular
    coefficients_hermitian initialState gridInitial b 0 k t hk (by simpa using ht)
  have hi : (fun x => IndependentTarget.rawFourier 0 mesh gridInitial x -
      Exp014.solution coefficients initialState 0 x) = (0 : ℝ → E 2) := by
    funext x
    rw [reconstruction_initial, reference_initial, sub_self]
    rfl
  simpa only [hi, Exp015.spatialL2_zero, zero_add, sub_zero] using he

#print axioms spinor_ne_zero
#print axioms coefficients_regular
#print axioms coefficients_hermitian
#print axioms potential_apply
#print axioms matrixPotential_hermitian
#print axioms potential_matches_matrix
#print axioms potential_nonconstant
#print axioms reference_initial
#print axioms A_hermitian
#print axioms B_hermitian
#print axioms gridInitial_ne_zero
#print axioms reconstruction_initial
#print axioms spatial_defect
#print axioms spatial_defect_at_pi
#print axioms spatial_defect_nonzero
#print axioms actual_slab_certificate
end NDEAEvolve.Exp016.OneNodeCosine
