import Orthogonality
import Reconstruction

/-! Full centered Fourier reconstruction of arbitrary data on an odd periodic
grid. This module establishes algebraic sampling fidelity and periodicity;
it does not claim continuum L2 Parseval or any refinement estimate. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp016

/-- The full centered frequency set, represented without integer-band reindexing. -/
def oddFrequency (M : ℕ) (m : Fin (2*M+1)) : ℤ := (m.val : ℤ) - (M : ℤ)

def fourierCoefficient (M : ℕ) (h : ℝ) (y : Vec (Grid (2*M)))
    (m : Fin (2*M+1)) : E 2 :=
  ((2*M+1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin (2*M+1),
    phase (-((oddFrequency M m : ℝ)*((j.val : ℝ)*h))) • Exp011.nodeValue (2*M) y j

def fourierSynthesis (M : ℕ) (a : Fin (2*M+1) → E 2) (x : ℝ) : E 2 :=
  ∑ m : Fin (2*M+1), phase ((oddFrequency M m : ℝ)*x) • a m

def fourierReconstruction (M : ℕ) (h : ℝ) (y : Vec (Grid (2*M))) : ℝ → E 2 :=
  fourierSynthesis M (fourierCoefficient M h y)

theorem oddFrequency_injective (M : ℕ) : Function.Injective (oddFrequency M) := by
  intro m l h
  apply Fin.ext
  unfold oddFrequency at h
  omega

private theorem fourier_index_difference_not_dvd (n : ℕ) (j l : Fin (n+1))
    (hjl : j ≠ l) : ¬ ((n+1 : ℕ) : ℤ) ∣ (j.val : ℤ) - (l.val : ℤ) := by
  rintro ⟨a, ha⟩
  have he : (j.val : ℝ) - (l.val : ℝ) = ((n+1 : ℕ) : ℝ)*(a : ℝ) := by
    exact_mod_cast ha
  have hj : (j.val : ℝ) < ((n+1 : ℕ) : ℝ) := by exact_mod_cast j.isLt
  have hl : (l.val : ℝ) < ((n+1 : ℕ) : ℝ) := by exact_mod_cast l.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hab : -(1 : ℝ) < (a : ℝ) ∧ (a : ℝ) < 1 := by constructor <;> nlinarith
  have hai : (-1 : ℤ) < a ∧ a < 1 := by exact_mod_cast hab
  have ha0 : a = 0 := by omega
  apply hjl
  apply Fin.ext
  rw [ha0, mul_zero] at ha
  exact_mod_cast sub_eq_zero.mp ha

/-- The exact row identity for all centered frequencies of the full odd grid. -/
theorem oddFourier_kernel (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (j l : Fin (2*M+1)) :
    (∑ m : Fin (2*M+1),
      phase ((oddFrequency M m : ℝ)*((j.val : ℝ)*h)) *
        phase (-((oddFrequency M m : ℝ)*((l.val : ℝ)*h)))) =
      if j = l then ((2*M+1 : ℕ) : ℂ) else 0 := by
  classical
  by_cases hjl : j = l
  · subst l
    simp only [← phase_add, add_neg_cancel, phase_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ite_true]
  · rw [if_neg hjl]
    have he (m : Fin (2*M+1)) :
        phase ((oddFrequency M m : ℝ)*((j.val : ℝ)*h)) *
          phase (-((oddFrequency M m : ℝ)*((l.val : ℝ)*h))) =
        phase (-((M : ℝ)*((j.val : ℝ)-(l.val : ℝ))*h)) *
          phase (((j.val : ℝ)-(l.val : ℝ))*((m.val : ℝ)*h)) := by
      rw [← phase_add, ← phase_add]
      congr 1
      simp only [oddFrequency, Int.cast_sub, Int.cast_natCast]
      ring
    have hs : (∑ m : Fin (2*M+1),
        phase (((j.val : ℝ)-(l.val : ℝ))*((m.val : ℝ)*h))) = 0 := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        phase_sum_zero (2*M) h hmesh ((j.val : ℤ)-(l.val : ℤ))
          (fourier_index_difference_not_dvd (2*M) j l hjl)
    simp_rw [he]
    rw [← Finset.mul_sum, hs, mul_zero]

/-- Sampling the reconstruction recovers every node of arbitrary full-grid data. -/
theorem fourierReconstruction_at_node (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi)
    (y : Vec (Grid (2*M))) (j : Fin (2*M+1)) :
    fourierReconstruction M h y ((j.val : ℝ)*h) = Exp011.nodeValue (2*M) y j := by
  classical
  have hN : ((2*M+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*M+1 ≠ 0 by omega)
  unfold fourierReconstruction fourierSynthesis fourierCoefficient
  calc
    _ = ((2*M+1 : ℕ) : ℂ)⁻¹ • ∑ m : Fin (2*M+1), ∑ l : Fin (2*M+1),
        (phase ((oddFrequency M m : ℝ)*((j.val : ℝ)*h)) *
          phase (-((oddFrequency M m : ℝ)*((l.val : ℝ)*h)))) •
            Exp011.nodeValue (2*M) y l := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [smul_comm]
      simp only [Finset.smul_sum, smul_smul, mul_assoc]
    _ = ((2*M+1 : ℕ) : ℂ)⁻¹ • ∑ l : Fin (2*M+1),
        (∑ m : Fin (2*M+1),
          phase ((oddFrequency M m : ℝ)*((j.val : ℝ)*h)) *
            phase (-((oddFrequency M m : ℝ)*((l.val : ℝ)*h)))) •
              Exp011.nodeValue (2*M) y l := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = ((2*M+1 : ℕ) : ℂ)⁻¹ • (((2*M+1 : ℕ) : ℂ) • Exp011.nodeValue (2*M) y j) := by
      simp_rw [oddFourier_kernel M h hmesh j]
      simp
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ hN, one_smul]

/-- The existing full-grid sampling definition is an exact left inverse. -/
theorem sampleSolution_fourierReconstruction (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi) (y : Vec (Grid (2*M))) :
    Exp010.sampleSolution (2*M) h (fun _ => fourierReconstruction M h y) 0 = y := by
  ext p
  rcases p with ⟨j,b⟩
  have hn := fourierReconstruction_at_node M h hmesh y j
  exact congrArg (fun v : E 2 => v b) hn

theorem fourierReconstruction_injective (M : ℕ) (h : ℝ)
    (hmesh : ((2*M+1 : ℕ) : ℝ)*h = 2*Real.pi) :
    Function.Injective (fourierReconstruction M h) := by
  intro y z hyz
  have hs := congrArg (fun u : ℝ → E 2 =>
    Exp010.sampleSolution (2*M) h (fun _ => u) 0) hyz
  simpa only [sampleSolution_fourierReconstruction M h hmesh] using hs

theorem fourierSynthesis_periodic (M : ℕ) (a : Fin (2*M+1) → E 2) :
    Function.Periodic (fourierSynthesis M a) (2*Real.pi) := by
  intro x
  unfold fourierSynthesis
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun c : ℂ => c • a m) (integer_phase_periodic (oddFrequency M m) x)

theorem fourierReconstruction_periodic (M : ℕ) (h : ℝ) (y : Vec (Grid (2*M))) :
    Function.Periodic (fourierReconstruction M h y) (2*Real.pi) :=
  fourierSynthesis_periodic M (fourierCoefficient M h y)

#print axioms oddFrequency_injective
#print axioms oddFourier_kernel
#print axioms fourierReconstruction_at_node
#print axioms sampleSolution_fourierReconstruction
#print axioms fourierReconstruction_injective
#print axioms fourierSynthesis_periodic
#print axioms fourierReconstruction_periodic
end NDEAEvolve.Exp016
