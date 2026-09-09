import SampledCayleyCertificate
import SpatialL2Bridge

/-! Separate the actual centered-stencil and sampled-potential discrepancies.
The identities retain the actual second derivative and potential multiplication.
The norm estimate separates their contributions without assuming either small. -/
noncomputable section
open scoped BigOperators Matrix Kronecker
open Set
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

namespace RegularSynthesis
variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {L : ℝ} (S : RegularSynthesis X H L)

def stencilDefect (K : X →L[ℂ] X) (x : ℝ) : X →L[ℂ] H :=
  (S.eval x).comp K + S.dxx x

def potentialDefect (P : X →L[ℂ] X) (V : ℝ → H →L[ℂ] H) (x : ℝ) : X →L[ℂ] H :=
  (S.eval x).comp P - (V x).comp (S.eval x)

theorem spatialDefect_split (K P : X →L[ℂ] X) (V : ℝ → H →L[ℂ] H) (x : ℝ) :
    S.spatialDefect (K + P) V x = S.stencilDefect K x + S.potentialDefect P V x := by
  ext z
  simp only [spatialDefect, stencilDefect, potentialDefect,
    _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, map_add]
  abel

theorem stencilDefect_apply_continuous (K : X →L[ℂ] X) (z : X) :
    Continuous (fun x => S.stencilDefect K x z) :=
  (S.continuous_eval.clm_apply continuous_const).add
    (S.continuous_dxx.clm_apply continuous_const)

theorem potentialDefect_apply_continuous (P : X →L[ℂ] X)
    (V : ℝ → H →L[ℂ] H) (hV : Continuous V) (z : X) :
    Continuous (fun x => S.potentialDefect P V x z) :=
  (S.continuous_eval.clm_apply continuous_const).sub
    (hV.clm_apply (S.continuous_eval.clm_apply continuous_const))

theorem spatialDefect_split_spatialL2_le [CompleteSpace H] (K P : X →L[ℂ] X)
    (V : ℝ → H →L[ℂ] H) (hV : Continuous V) (z : X) (b : ℝ) (hL : 0 ≤ L) :
    Exp015.spatialL2 (fun x => S.spatialDefect (K + P) V x z) b L ≤
      Exp015.spatialL2 (fun x => S.stencilDefect K x z) b L +
      Exp015.spatialL2 (fun x => S.potentialDefect P V x z) b L := by
  simp_rw [S.spatialDefect_split, _root_.add_apply]
  exact spatialL2_add_le _ _ b L hL
    (S.stencilDefect_apply_continuous K z) (S.potentialDefect_apply_continuous P V hV z)

end RegularSynthesis

def gridKinetic (n : ℕ) (h : ℝ) : Matrix (Grid n) (Grid n) ℂ :=
  PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)

def sampledStencilDefect (M : ℕ) (h x : ℝ) : Vec (Grid (2 * M)) →L[ℂ] E 2 :=
  (fourierRegularSynthesis M h).stencilDefect (op (gridKinetic (2 * M) h)) x

def sampledPotentialDefect (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (x : ℝ) : Vec (Grid (2 * M)) →L[ℂ] E 2 :=
  (fourierRegularSynthesis M h).potentialDefect
    (op (sampledBlock (2 * M) h (operatorPotentialMatrix v))) (Exp014.operatorPotential v) x

theorem sampled_generator_decomposition (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) :
    op (sampledSplitA n h) + op (sampledSplitB n h (operatorPotentialMatrix v)) =
      op (gridKinetic n h) + op (sampledBlock n h (operatorPotentialMatrix v)) := by
  rw [← map_add, sampledSplit_sum, map_add]
  rfl

/-- This is the actual second derivative, not an independently supplied field. -/
theorem sampledStencilDefect_apply (M : ℕ) (h x : ℝ) (z : Vec (Grid (2 * M))) :
    sampledStencilDefect M h x z =
      fourierReconstruction M h (op (gridKinetic (2 * M) h) z) x +
        deriv (deriv (fourierReconstruction M h z)) x := by
  have hd := (fourierRegularSynthesis M h).field_second_space_derivative (fun _ => z) 0 x
  rw [fourierRegularSynthesis_field] at hd
  change deriv (deriv (fourierReconstruction M h z)) x = _ at hd
  simp only [sampledStencilDefect, RegularSynthesis.stencilDefect,
    _root_.add_apply, ContinuousLinearMap.comp_apply, fourierRegularSynthesis_eval]
  rw [hd]

theorem sampledPotentialDefect_apply (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (x : ℝ) (z : Vec (Grid (2 * M))) :
    sampledPotentialDefect M h v x z =
      fourierReconstruction M h (op (sampledBlock (2 * M) h (operatorPotentialMatrix v)) z) x -
        Exp014.operatorPotential v x (fourierReconstruction M h z x) := by
  simp only [sampledPotentialDefect, RegularSynthesis.potentialDefect,
    _root_.sub_apply, ContinuousLinearMap.comp_apply, fourierRegularSynthesis_eval]

theorem sampled_spatialDefect_split (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (x : ℝ) :
    (fourierRegularSynthesis M h).spatialDefect
      (op (sampledSplitA (2 * M) h) + op (sampledSplitB (2 * M) h (operatorPotentialMatrix v)))
      (Exp014.operatorPotential v) x = sampledStencilDefect M h x + sampledPotentialDefect M h v x := by
  rw [sampled_generator_decomposition, RegularSynthesis.spatialDefect_split]
  rfl

def sampledSpatialDefectBudget (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (z : Vec (Grid (2 * M))) (b : ℝ) : ℝ :=
  Exp015.spatialL2 (fun x => sampledStencilDefect M h x z) b (2 * Real.pi) +
    Exp015.spatialL2 (fun x => sampledPotentialDefect M h v x z) b (2 * Real.pi)

theorem sampled_spatialDefect_spatialL2_le (M : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (z : Vec (Grid (2 * M))) (b : ℝ) :
    Exp015.spatialL2 (fun x => (fourierRegularSynthesis M h).spatialDefect
      (op (sampledSplitA (2 * M) h) + op (sampledSplitB (2 * M) h (operatorPotentialMatrix v)))
      (Exp014.operatorPotential v) x z) b (2 * Real.pi) ≤ sampledSpatialDefectBudget M h v z b := by
  rw [sampled_generator_decomposition]
  exact (fourierRegularSynthesis M h).spatialDefect_split_spatialL2_le _ _ _
    (Exp014.operatorPotential_continuous v hv) z b (by positivity)

#print axioms RegularSynthesis.spatialDefect_split
#print axioms RegularSynthesis.stencilDefect_apply_continuous
#print axioms RegularSynthesis.potentialDefect_apply_continuous
#print axioms RegularSynthesis.spatialDefect_split_spatialL2_le
#print axioms sampled_generator_decomposition
#print axioms sampledStencilDefect_apply
#print axioms sampledPotentialDefect_apply
#print axioms sampled_spatialDefect_split
#print axioms sampled_spatialDefect_spatialL2_le
end NDEAEvolve.Exp016
