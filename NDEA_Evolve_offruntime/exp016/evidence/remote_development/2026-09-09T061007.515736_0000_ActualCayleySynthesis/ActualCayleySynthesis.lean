import QuadraticCayleyBridge
import FourierSynthesisRegular
import QuadraticPDEBudget

/-! Actual ordered Cayley stages supply a regular full-grid Fourier slab and
a computed PDE residual budget. The potential/stencil discrepancy remains
explicit; no relation between the grid matrices and V is silently assumed. -/
noncomputable section
open Set
open NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

section OrderedStages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orderedCayleyEndpoint (A B : Matrix ι ι ℂ) (k : ℝ) (u₀ : Vec ι) : Vec ι :=
  step (k / 4) A (step (k / 2) B (step (k / 4) A u₀))

def orderedCayleyInternalDefect (A B : Matrix ι ι ℂ) (k : ℝ) (u₀ : Vec ι) : Vec ι :=
  internalMeanDefect u₀ (step (k / 4) A u₀)
    (step (k / 2) B (step (k / 4) A u₀)) (orderedCayleyEndpoint A B k u₀)

def orderedCayleySplitDefect (A B : Matrix ι ι ℂ) (k : ℝ) (u₀ : Vec ι) : Vec ι :=
  (1 / 2 : ℂ) • op A (orderedCayleyInternalDefect A B k u₀) +
    op B (orderedCayleyInternalDefect A B k u₀)

theorem orderedCayley_midpointDefect (A B : Matrix ι ι ℂ) (k : ℝ)
    (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian) (u₀ : Vec ι) :
    quadraticMidpointDefect (op A + op B) u₀ (orderedCayleyEndpoint A B k u₀) k =
      orderedCayleySplitDefect A B k u₀ :=
  actual_cayley_quadraticMidpointDefect A B k hk hA hB u₀

end OrderedStages

def actualFourierQuadratic (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (u₀ : Vec (Grid (2 * M))) (t₀ k t x : ℝ) : E 2 :=
  fourierReconstruction M h
    (quadraticSlab (op A + op B) u₀ (orderedCayleyEndpoint A B k u₀) t₀ k t) x

/-- The three spatial terms are actual synthesis/operator discrepancies. -/
def actualFourierResidualBudget (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (V : ℝ → E 2 →L[ℂ] E 2) (u₀ : Vec (Grid (2 * M))) (b k : ℝ) : ℝ :=
  let G := op A + op B
  let u₃ := orderedCayleyEndpoint A B k u₀
  let m := quadraticMean u₀ u₃
  let v := quadraticVelocity u₀ u₃ k
  let S := fourierRegularSynthesis M h
  Real.sqrt h * (‖orderedCayleySplitDefect A B k u₀‖ + (k ^ 2 / 8) * ‖G (G v)‖) +
    Exp015.spatialL2 (fun x => S.spatialDefect G V x m) b (2 * Real.pi) +
    (k / 2) * Exp015.spatialL2 (fun x => S.spatialDefect G V x v) b (2 * Real.pi) +
    (k ^ 2 / 8) * Exp015.spatialL2 (fun x => S.spatialDefect G V x (G v)) b (2 * Real.pi)

theorem actualFourierQuadratic_regular (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (u₀ : Vec (Grid (2 * M))) (t₀ k : ℝ) :
    Exp015.IsRegularPeriodicField (2 * Real.pi) (actualFourierQuadratic M h A B u₀ t₀ k) :=
  fourier_quadratic_regular M h (op A + op B)
    (quadraticMean u₀ (orderedCayleyEndpoint A B k u₀))
    (quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k) t₀ k

theorem actualFourierQuadratic_left (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (u₀ : Vec (Grid (2 * M))) (t₀ k x : ℝ) (hk : k ≠ 0) :
    actualFourierQuadratic M h A B u₀ t₀ k t₀ x = fourierReconstruction M h u₀ x := by
  rw [actualFourierQuadratic, quadraticSlab_left _ _ _ _ _ hk]

theorem actualFourierQuadratic_right (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (u₀ : Vec (Grid (2 * M))) (t₀ k x : ℝ) (hk : k ≠ 0) :
    actualFourierQuadratic M h A B u₀ t₀ k (t₀ + k) x =
      fourierReconstruction M h (orderedCayleyEndpoint A B k u₀) x := by
  rw [actualFourierQuadratic, quadraticSlab_right _ _ _ _ _ hk]

theorem actualFourierQuadratic_residual (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (V : ℝ → E 2 →L[ℂ] E 2) (u₀ : Vec (Grid (2 * M))) (t₀ k t x : ℝ)
    (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Exp015.pdeResidual (fun _ => V) (actualFourierQuadratic M h A B u₀ t₀ k) t x =
      fourierReconstruction M h (orderedCayleySplitDefect A B k u₀) x +
        quadraticCorrection t₀ k t • fourierReconstruction M h
          ((op A + op B) ((op A + op B)
            (quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k))) x +
        (fourierRegularSynthesis M h).spatialDefect (op A + op B) V x
          (quadraticSlab (op A + op B) u₀ (orderedCayleyEndpoint A B k u₀) t₀ k t) := by
  have he : actualFourierQuadratic M h A B u₀ t₀ k =
      (fourierRegularSynthesis M h).field
        (quadraticTime (op A + op B)
          (quadraticMean u₀ (orderedCayleyEndpoint A B k u₀))
          (quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k) t₀ k) := by
    funext s y
    exact (fourierRegularSynthesis_eval M h y _).symm
  have hd := orderedCayley_midpointDefect A B k hk hA hB u₀
  unfold quadraticMidpointDefect at hd
  rw [he, RegularSynthesis.quadratic_field_residual, hd]
  simp only [fourierRegularSynthesis_eval, quadraticSlab]

theorem actualFourierQuadratic_residual_spatialL2_le (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (V : ℝ → E 2 →L[ℂ] E 2) (hV : Continuous V)
    (u₀ : Vec (Grid (2 * M))) (b t₀ k t : ℝ)
    (hk : k ≠ 0) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ht : t ∈ Icc t₀ (t₀ + k)) :
    Exp015.spatialL2
      (Exp015.pdeResidual (fun _ => V) (actualFourierQuadratic M h A B u₀ t₀ k) t)
        b (2 * Real.pi) ≤ actualFourierResidualBudget M h A B V u₀ b k := by
  have hb := fourier_quadratic_residual_spatialL2_le M h hmesh (op A + op B) V hV
    (quadraticMean u₀ (orderedCayleyEndpoint A B k u₀))
    (quadraticVelocity u₀ (orderedCayleyEndpoint A B k u₀) k) b t₀ k t ht
  have hd := orderedCayley_midpointDefect A B k hk hA hB u₀
  unfold quadraticMidpointDefect at hd
  rw [hd] at hb
  exact hb

#print axioms orderedCayley_midpointDefect
#print axioms actualFourierQuadratic_regular
#print axioms actualFourierQuadratic_left
#print axioms actualFourierQuadratic_right
#print axioms actualFourierQuadratic_residual
#print axioms actualFourierQuadratic_residual_spatialL2_le

end NDEAEvolve.Exp016
