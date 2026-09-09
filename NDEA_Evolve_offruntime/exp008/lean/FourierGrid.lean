import Exp007Foundation
import FrequencyBounds

/-! Integer Fourier modes on the actual periodic spinor grid. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp008.FourierGrid

def modeLift (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => phase ((m : ℝ) * ((p.1.val : ℝ) * h)) * v p.2)

def modeLiftLinear (n : ℕ) (h : ℝ) (m : ℤ) : E 2 →ₗ[ℂ] Vec (Grid n) where
  toFun := modeLift n h m
  map_add' := by
    intro u v
    ext p
    change phase _ * (u p.2 + v p.2) = phase _ * u p.2 + phase _ * v p.2
    ring
  map_smul' := by
    intro c v
    ext p
    change phase _ * (c * v p.2) = c * (phase _ * v p.2)
    ring

def modeLiftCLM (n : ℕ) (h : ℝ) (m : ℤ) : E 2 →L[ℂ] Vec (Grid n) :=
  (modeLiftLinear n h m).toContinuousLinearMap

@[simp] theorem modeLiftCLM_apply (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) : modeLiftCLM n h m v = modeLift n h m v := rfl

theorem modeLift_norm_sq (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) :
    ‖modeLift n h m v‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [modeLift, Fintype.sum_prod_type, norm_mul]
  ring

theorem modeLift_weighted_norm (n : ℕ) (h : ℝ) (m : ℤ) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    Real.sqrt h * ‖modeLift n h m v‖ = Real.sqrt (2 * Real.pi) * ‖v‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), modeLift_norm_sq]
  nlinarith [hmesh]


theorem integer_phase_periodic (m : ℤ) :
    Function.Periodic (fun x : ℝ => phase ((m : ℝ) * x)) (2 * Real.pi) := by
  intro x
  change phase ((m : ℝ) * (x + 2 * Real.pi)) = phase ((m : ℝ) * x)
  rw [mul_add]
  exact (phase_periodic.int_mul m) ((m : ℝ) * x)

theorem mode_centeredStencil (m : ℤ) (h x : ℝ) :
    centeredStencil h (fun x => phase ((m : ℝ) * x)) x =
      (modeSymbol m h : ℂ) * phase ((m : ℝ) * x) := by
  have hadd : phase ((m : ℝ)*(x+h)) = phase ((m : ℝ)*x) * phase ((m : ℝ)*h) := by
    rw [mul_add, phase_add]
  have hsub : phase ((m : ℝ)*(x-h)) = phase ((m : ℝ)*x) * phase (-((m : ℝ)*h)) := by
    rw [mul_sub, sub_eq_add_neg, phase_add]
  have hsum : phase ((m : ℝ)*h) + phase (-((m : ℝ)*h)) =
      (2 * Real.cos ((m : ℝ)*h) : ℝ) := by
    rw [phase_formula, phase_formula]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  unfold centeredStencil modeSymbol
  dsimp only
  rw [hadd, hsub]
  push_cast
  calc
    _ = (2-(phase ((m : ℝ)*h)+phase (-((m : ℝ)*h)))) / (h : ℂ)^2 *
        phase ((m : ℝ)*x) := by ring
    _ = _ := by rw [hsum]; push_cast; ring

theorem potential_modeLift (n : ℕ) (h : ℝ) (m : ℤ) (K : Mat 2) (v : E 2) :
    op (potential n K) (modeLiftCLM n h m v) = modeLiftCLM n h m (operatorOf K v) := by
  ext p
  rcases p with ⟨i,a⟩
  rw [potential_apply]
  change (∑ b : Fin 2, K a b * (phase ((m : ℝ)*((i.val : ℝ)*h)) * v b)) =
    phase ((m : ℝ)*((i.val : ℝ)*h)) * (K.mulVec (WithLp.ofLp v) a)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem laplacian_modeLift (n : ℕ) (h : ℝ) (m : ℤ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) (modeLiftCLM n h m v) =
      (modeSymbol m h : ℂ) • modeLiftCLM n h m v := by
  ext p
  rcases p with ⟨i,a⟩
  rw [laplacian_apply]
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((m : ℝ)*((j.val : ℝ)*h)) * v a) i =
      (modeSymbol m h : ℂ) * (phase ((m : ℝ)*((i.val : ℝ)*h)) * v a)
  have hf : Function.Periodic (fun x => phase ((m : ℝ)*x) * v a) (2*Real.pi) := by
    intro x
    change phase ((m : ℝ)*(x + 2 * Real.pi)) * v a = phase ((m : ℝ)*x) * v a
    exact congrArg (fun z : ℂ => z * v a) (integer_phase_periodic m x)
  have hs := PeriodicGrid.matrix_sample_stencil (n := n) (2*Real.pi) h
    (fun x => phase ((m : ℝ)*x) * v a) hf hmesh i
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((m : ℝ)*((j.val : ℝ)*h)) * v a) i = _ at hs
  rw [hs]
  have hc := mode_centeredStencil m h ((i.val : ℝ)*h)
  unfold centeredStencil at hc
  dsimp only at hc
  calc
    _ = ((2*phase ((m : ℝ)*((i.val : ℝ)*h)) - phase ((m : ℝ)*((i.val : ℝ)*h+h)) -
      phase ((m : ℝ)*((i.val : ℝ)*h-h)))/(h : ℂ)^2) * v a := by ring
    _ = _ := by rw [hc]; ring

theorem hamiltonian_modeLift (n : ℕ) (h : ℝ) (m : ℤ) (K : Mat 2)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (hamiltonian n h K) (modeLiftCLM n h m v) =
      modeLiftCLM n h m (operatorOf ((modeSymbol m h : ℂ) • 1 + K) v) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, laplacian_modeLift n h m hmesh,
    potential_modeLift, operatorOf, map_smul, map_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
theorem hamiltonian_step_modeLift (n : ℕ) (h a : ℝ) (m : ℤ) (K : Mat 2) (hK : K.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    step a (hamiltonian n h K) (modeLiftCLM n h m v) =
      modeLiftCLM n h m (Chat ((modeSymbol m h : ℂ) • 1 + K) a v) := by
  exact step_intertwines (modeLiftCLM n h m) (hamiltonian n h K) _
    (hamiltonian_isHermitian n h K hK) (scalar_add_isHermitian _ K hK)
    (hamiltonian_modeLift n h m K hmesh) a v

theorem potential_step_modeLift (n : ℕ) (h a : ℝ) (m : ℤ) (K : Mat 2) (hK : K.IsHermitian)
    (v : E 2) :
    step a (potential n K) (modeLiftCLM n h m v) = modeLiftCLM n h m (Chat K a v) := by
  exact step_intertwines (modeLiftCLM n h m) (potential n K) K
    (potential_isHermitian n K hK) hK (potential_modeLift n h m K) a v
theorem symmetric_modeLift (n : ℕ) (h k : ℝ) (m : ℤ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    symmetric n h k K Q (modeLiftCLM n h m v) =
      modeLiftCLM n h m (symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k v) := by
  simp only [symmetric, symmetricStepHat, ContinuousLinearMap.mul_apply,
    hamiltonian_step_modeLift n h _ m K hK hmesh, potential_step_modeLift n h _ m Q hQ]

theorem symmetric_pow_modeLift (n : ℕ) (h k : ℝ) (m : ℤ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (v : E 2) :
    (symmetric n h k K Q ^ N) (modeLiftCLM n h m v) =
      modeLiftCLM n h m ((symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k ^ N) v) := by
  induction N generalizing v with
  | zero => simp
  | succ N ih =>
    simp only [pow_succ, ContinuousLinearMap.mul_apply,
      symmetric_modeLift n h k m K Q hK hQ hmesh, ih]


def superpositionLift (n : ℕ) (h : ℝ) (S : Finset ℤ) (a : ℤ → E 2) : Vec (Grid n) :=
  ∑ m ∈ S, modeLiftCLM n h m (a m)

theorem symmetric_pow_superposition (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ)
    (S : Finset ℤ) (a : ℤ → E 2) :
    (symmetric n h k K Q ^ N) (superpositionLift n h S a) =
      superpositionLift n h S (fun m =>
        (symmetricStepHat ((modeSymbol m h : ℂ) • 1 + K) Q k ^ N) (a m)) := by
  simp only [superpositionLift, map_sum, symmetric_pow_modeLift n h k _ K Q hK hQ hmesh]

end NDEAEvolve.Exp008.FourierGrid
