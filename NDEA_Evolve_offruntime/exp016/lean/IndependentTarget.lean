import Reconstruction

/-! Independent reconstruction target, stated using sealed numerical APIs only.
No Exp016 implementation module is imported. These definitions specify the
physical field to which the implementation's certificate must be connected;
they do not prove its regularity, residual bound, or convergence. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016.IndependentTarget

/-- The full centered inverse DFT, with raw sampled coefficients and the
unnormalized physical spatial coordinate. -/
def rawFourier (M : ℕ) (h : ℝ) (y : Vec (Grid (2 * M))) (x : ℝ) : E 2 :=
  ∑ m : Fin (2 * M + 1),
    phase (((m.val : ℤ) - (M : ℤ) : ℝ) * x) •
      ((((2 * M + 1 : ℕ) : ℂ)⁻¹) •
        ∑ j : Fin (2 * M + 1),
          phase (-(((m.val : ℤ) - (M : ℤ) : ℝ) * ((j.val : ℝ) * h))) •
            Exp011.nodeValue (2 * M) y j)

/-- The raw centered quadratic endpoint polynomial. Its velocity divides by
k, so later endpoint/certificate theorems must retain the appropriate k≠0
or k>0 assumption. The definition itself makes no endpoint claim at k=0. -/
def rawQuadratic {ι : Type*} [Fintype ι]
    (G : Vec ι →L[ℂ] Vec ι) (y₀ y₃ : Vec ι) (t₀ k t : ℝ) : Vec ι :=
  let m := (1 / 2 : ℂ) • (y₀ + y₃)
  let v := (k : ℂ)⁻¹ • (y₃ - y₀)
  let s : ℝ := t - (t₀ + k / 2)
  m + (s : ℂ) • v - ((Complex.I / 2) * ((s : ℂ) ^ 2 - (k : ℂ) ^ 2 / 4)) • G v

/-- Exact action order from the sealed full-grid Cayley definition. -/
def cayleyEndpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (k : ℝ) (y₀ : Vec ι) : Vec ι :=
  step (k / 4) A (step (k / 2) B (step (k / 4) A y₀))

/-- The actual Cayley endpoints, full DFT and centered time polynomial are
specified together. A and B must later be identified with the concrete
centered stencil/Pauli and sampled-potential-minus-Pauli matrices. -/
def actualCayleyFourierSlab (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (y₀ : Vec (Grid (2 * M))) (t₀ k t x : ℝ) : E 2 :=
  rawFourier M h
    (rawQuadratic (op A + op B) y₀ (cayleyEndpoint A B k y₀) t₀ k t) x

/-- A definition-binding target, not a residual-smallness or regularity axiom. -/
def RealizesActualCayleySlab (M : ℕ) (h : ℝ)
    (A B : Matrix (Grid (2 * M)) (Grid (2 * M)) ℂ)
    (y₀ : Vec (Grid (2 * M))) (t₀ k : ℝ) (w : ℝ → ℝ → E 2) : Prop :=
  ∀ t x, w t x = actualCayleyFourierSlab M h A B y₀ t₀ k t x

end NDEAEvolve.Exp016.IndependentTarget
