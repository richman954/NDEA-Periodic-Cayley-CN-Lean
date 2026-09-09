import ActualCayleyCertificate
import SampledPotential

/-! The actual centered stencil and sampled Exp014 potential instantiate the
finite-trajectory certificate. The matrix field is the inverse of Mathlib's
star-algebra equivalence, so no unrelated matrix or compatibility hypothesis
is supplied. Arbitrary numerical initial data and positive variable steps are
retained. This is an analytical residual certificate, not a refinement result. -/
noncomputable section
open scoped BigOperators Matrix Kronecker
open Set
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

/-- The unique matrix representing the actual continuum potential on E 2. -/
def operatorPotentialMatrix (v : ℤ → E 2 →L[ℂ] E 2) (x : ℝ) : Mat 2 :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm (Exp014.operatorPotential v x)

theorem operatorPotentialMatrix_represents (v : ℤ → E 2 →L[ℂ] E 2) (x : ℝ) :
    operatorOf (operatorPotentialMatrix v x) = Exp014.operatorPotential v x :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).apply_symm_apply _

theorem operatorPotentialMatrix_isHermitian (v : ℤ → E 2 →L[ℂ] E 2)
    (hHerm : Exp014.HermitianFourierPotential v) (x : ℝ) :
    (operatorPotentialMatrix v x).IsHermitian :=
  ((Exp014.operatorPotential_selfAdjoint v hHerm x).map
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm).isHermitian

/-- Sampling this matrix field is exactly application of the original
operator-valued Fourier potential at the physical grid node. -/
theorem sampled_operatorPotential_nodeValue (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid n)) (i : Fin (n + 1)) :
    Exp011.nodeValue n (op (sampledBlock n h (operatorPotentialMatrix v)) y) i =
      Exp014.operatorPotential v ((i.val : ℝ) * h) (Exp011.nodeValue n y i) := by
  rw [sampledBlock_nodeValue, operatorPotentialMatrix_represents]

theorem sampled_operatorPotential_splitB_isHermitian (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hHerm : Exp014.HermitianFourierPotential v) :
    (sampledSplitB n h (operatorPotentialMatrix v)).IsHermitian :=
  sampledSplitB_isHermitian n h _ (operatorPotentialMatrix_isHermitian v hHerm)

/-- The sum of the concrete split factors has the prescribed centered
negative-Laplacian stencil plus the actual sampled continuum potential. -/
theorem sampled_operatorPotential_stencil (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (y : Vec (Grid n))
    (i : Fin (n + 1)) (a : Fin 2) :
    (op (sampledSplitA n h) + op (sampledSplitB n h (operatorPotentialMatrix v))) y (i, a) =
      (2 * y (i, a) - y (PeriodicGrid.next i, a) - y (PeriodicGrid.prev i, a)) /
        (h : ℂ)^2 +
      (Exp014.operatorPotential v ((i.val : ℝ) * h) (Exp011.nodeValue n y i)) a := by
  rw [← map_add, sampledSplit_sum, map_add]
  simp only [_root_.add_apply, PiLp.add_apply, laplacian_apply, PeriodicGrid.laplacian_mulVec]
  congr 1
  exact congrArg (fun z : E 2 => z a) (sampled_operatorPotential_nodeValue n h v y i)

/-- Actual ordered A-half/B-full/A-half recurrence for the sampled potential. -/
def sampledCayleyTrajectory (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (k : ℕ → ℝ) : ℕ → Vec (Grid (2 * M)) :=
  actualCayleyTrajectory (sampledSplitA (2 * M) h)
    (sampledSplitB (2 * M) h (operatorPotentialMatrix v)) y₀ k

def sampledCayleyBudgetSequence (M : ℕ) (h : ℝ) (v : ℤ → E 2 →L[ℂ] E 2)
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) : ℕ → ℝ :=
  actualCayleyBudgetSequence M h (sampledSplitA (2 * M) h)
    (sampledSplitB (2 * M) h (operatorPotentialMatrix v))
    (Exp014.operatorPotential v) y₀ b k

/-- No free Hermitian matrices remain: the finite grid-time estimate uses
the actual stencil, sampled potential and recursively computed trajectory. -/
theorem sampledCayley_gridTime_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ)
    (hk : ∀ j < N, 0 < k j) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.rawFourier M h (sampledCayleyTrajectory M h v y₀ k N) x -
        Exp014.solution v a (actualCayleyTime k N) x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      ∑ j ∈ Finset.range N, k j * sampledCayleyBudgetSequence M h v y₀ b k j :=
  actualCayley_gridTime_error M h hmesh (sampledSplitA (2 * M) h)
    (sampledSplitB (2 * M) h (operatorPotentialMatrix v))
    (sampledSplitA_isHermitian (2 * M) h)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h v hHerm)
    v hv hHerm a y₀ b k N hk

/-- The same concrete trajectory also has the certificate at every point of
a final partial slab, with its elapsed duration and actual computed budget. -/
theorem sampledCayley_partialSlab_error (M : ℕ) (h : ℝ)
    (hmesh : ((2 * M + 1 : ℕ) : ℝ) * h = 2 * Real.pi)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v)
    (hHerm : Exp014.HermitianFourierPotential v) (a : Exp014.FourierState (E 2))
    (y₀ : Vec (Grid (2 * M))) (b : ℝ) (k : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hk : ∀ j < N, 0 < k j) (hkN : 0 < k N)
    (ht : t ∈ Icc (actualCayleyTime k N) (actualCayleyTime k N + k N)) :
    Exp015.spatialL2 (fun x =>
      IndependentTarget.actualCayleyFourierSlab M h (sampledSplitA (2 * M) h)
        (sampledSplitB (2 * M) h (operatorPotentialMatrix v))
        (sampledCayleyTrajectory M h v y₀ k N) (actualCayleyTime k N) (k N) t x -
        Exp014.solution v a t x) b (2 * Real.pi) ≤
      Exp015.spatialL2 (fun x => IndependentTarget.rawFourier M h y₀ x -
        Exp014.synth a x) b (2 * Real.pi) +
      (∑ j ∈ Finset.range N, k j * sampledCayleyBudgetSequence M h v y₀ b k j) +
      (t - actualCayleyTime k N) * sampledCayleyBudgetSequence M h v y₀ b k N :=
  actualCayley_partialSlab_error M h hmesh (sampledSplitA (2 * M) h)
    (sampledSplitB (2 * M) h (operatorPotentialMatrix v))
    (sampledSplitA_isHermitian (2 * M) h)
    (sampled_operatorPotential_splitB_isHermitian (2 * M) h v hHerm)
    v hv hHerm a y₀ b k N t hk hkN ht

#print axioms operatorPotentialMatrix_represents
#print axioms operatorPotentialMatrix_isHermitian
#print axioms sampled_operatorPotential_nodeValue
#print axioms sampled_operatorPotential_splitB_isHermitian
#print axioms sampled_operatorPotential_stencil
#print axioms sampledCayley_gridTime_error
#print axioms sampledCayley_partialSlab_error
end NDEAEvolve.Exp016
