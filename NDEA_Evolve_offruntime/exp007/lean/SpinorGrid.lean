import CombinedVerification
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Full periodic spinor grid and its invariant first Fourier mode. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp004 NDEAEvolve.Exp006

namespace NDEAEvolve.Exp007.SpinorGrid

section GenericCayley
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vec (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev op (H : Matrix ι ι ℂ) : Vec ι →L[ℂ] Vec ι :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) H
def den (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 + (Complex.I * (a : ℂ)) • H
def num (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := 1 - (Complex.I * (a : ℂ)) • H
def resolvent (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := (den a H)⁻¹
def cayleyMatrix (a : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := num a H * resolvent a H
abbrev step (a : ℝ) (H : Matrix ι ι ℂ) := op (cayleyMatrix a H)

theorem den_star (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    star (den a H) = num a H := by
  have hs : star H = H := hH.eq
  simp [den, num, star_smul, hs, sub_eq_add_neg]

theorem den_isUnit (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    IsUnit (den a H) := by
  have hs : star ((Complex.I * (a : ℂ)) • H) = -((Complex.I * (a : ℂ)) • H) := by
    have hstar : star H = H := hH.eq
    simp [star_smul, hstar]
  have hg : star (den a H) * den a H =
      1 + star ((Complex.I * (a : ℂ)) • H) * ((Complex.I * (a : ℂ)) • H) := by
    rw [den_star a H hH, hs]
    unfold num den
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  have hp : Matrix.PosDef (star (den a H) * den a H) := by
    rw [hg]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self _)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hp.isUnit
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply hi
  simpa only [Matrix.mulVec_mulVec] using
    congrArg (fun z => (star (den a H)).mulVec z) hxy

theorem den_mul_resolvent (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    den a H * resolvent a H = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (den_isUnit a H hH))

theorem resolvent_mul_den (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    resolvent a H * den a H = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (den_isUnit a H hH))

theorem den_step (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    den a H * cayleyMatrix a H = num a H := by
  have hc : den a H * num a H = num a H * den a H := by
    unfold den num
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  rw [cayleyMatrix, ← Matrix.mul_assoc, hc, Matrix.mul_assoc, den_mul_resolvent a H hH,
    Matrix.mul_one]

/-- Each full-grid Crank--Nicolson stage has exactly one solution. -/
theorem stage_unique (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (u v : Vec ι) :
    op (den a H) v = op (num a H) u ↔ v = step a H u := by
  have hi : Function.Injective (op (den a H)) := by
    intro x y hxy
    have hp := congrArg (op (resolvent a H)) hxy
    have hid : op (resolvent a H) * op (den a H) = 1 := by
      rw [← map_mul, resolvent_mul_den a H hH, map_one]
    simpa only [← ContinuousLinearMap.mul_apply, hid, ContinuousLinearMap.one_apply] using hp
  have heq : op (den a H) (step a H u) = op (num a H) u := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, den_step a H hH]
  exact ⟨fun h => hi (h.trans heq.symm), fun h => h ▸ heq⟩

end GenericCayley

theorem den_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    op (den a H) (J v) = J (op (den a K) v) := by
  simp only [den, map_add, map_one, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, hJK]

theorem num_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    op (num a H) (J v) = J (op (num a K) v) := by
  simp only [num, map_sub, map_one, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, hJK]

/-- A generator intertwiner also intertwines the actual inverse Cayley factors. -/
theorem step_intertwines {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (J : Vec κ →L[ℂ] Vec ι)
    (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hJK : ∀ v, op H (J v) = J (op K v)) (a : ℝ) (v : Vec κ) :
    step a H (J v) = J (step a K v) := by
  have hd := den_intertwines J H K hJK a
  have hn := num_intertwines J H K hJK a
  apply ((stage_unique a H hH (J v) (J (step a K v))).mp ?_).symm
  rw [hd, hn]
  exact congrArg J ((stage_unique a K hK v (step a K v)).mpr rfl)

abbrev Grid (n : ℕ) := Fin (n + 1) × Fin 2

def lift (n : ℕ) (h : ℝ) (v : E 2) : Vec (Grid n) :=
  WithLp.toLp 2 (fun p => phase ((p.1.val : ℝ) * h) * v p.2)

def liftLinear (n : ℕ) (h : ℝ) : E 2 →ₗ[ℂ] Vec (Grid n) where
  toFun := lift n h
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

def liftCLM (n : ℕ) (h : ℝ) : E 2 →L[ℂ] Vec (Grid n) :=
  (liftLinear n h).toContinuousLinearMap

@[simp] theorem liftCLM_apply (n : ℕ) (h : ℝ) (v : E 2) : liftCLM n h v = lift n h v := rfl

theorem lift_norm_sq (n : ℕ) (h : ℝ) (v : E 2) :
    ‖lift n h v‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [lift, Fintype.sum_prod_type, norm_mul]
  ring

theorem lift_weighted_norm (n : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    Real.sqrt h * ‖lift n h v‖ = Real.sqrt (2 * Real.pi) * ‖v‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hh,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi), lift_norm_sq]
  nlinarith [hmesh]


theorem step_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    step a H ∈ unitary (Vec ι →L[ℂ] Vec ι) := by
  have hn : den a H * star (den a H) = star (den a H) * den a H := by
    rw [den_star a H hH]
    unfold den num
    generalize ((Complex.I * (a : ℂ)) • H) = S
    noncomm_ring
  have hu := unitary_of_normal_and_inverse (den a H) (resolvent a H) hn
    (den_mul_resolvent a H hH) (resolvent_mul_den a H hH)
  rw [den_star a H hH] at hu
  change cayleyMatrix a H * star (cayleyMatrix a H) = 1 ∧
    star (cayleyMatrix a H) * cayleyMatrix a H = 1 at hu
  rw [Unitary.mem_iff]
  constructor
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M) hu.2
  · simpa only [map_mul, map_one, map_star] using congrArg
      (fun M : Matrix ι ι ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M) hu.1

def potential (n : ℕ) (K : Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  (1 : Mat (n + 1)) ⊗ₖ K

def hamiltonian (n : ℕ) (h : ℝ) (K : Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2) + potential n K

theorem potential_isHermitian (n : ℕ) (K : Mat 2) (hK : K.IsHermitian) :
    (potential n K).IsHermitian := by
  unfold potential Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hK.eq]

theorem hamiltonian_isHermitian (n : ℕ) (h : ℝ) (K : Mat 2) (hK : K.IsHermitian) :
    (hamiltonian n h K).IsHermitian := by
  unfold hamiltonian
  apply Matrix.IsHermitian.add _ (potential_isHermitian n K hK)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (PeriodicGrid.isHermitian n h).eq]

theorem potential_apply (n : ℕ) (K : Mat 2) (u : Vec (Grid n))
    (i : Fin (n + 1)) (a : Fin 2) :
    op (potential n K) u (i,a) = ∑ b : Fin 2, K a b * u (i,b) := by
  change (potential n K).mulVec (WithLp.ofLp u) (i,a) = _
  simp [potential, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

theorem laplacian_apply (n : ℕ) (h : ℝ) (u : Vec (Grid n))
    (i : Fin (n + 1)) (a : Fin 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) u (i,a) =
      (PeriodicGrid.laplacian n h).mulVec (fun j => u (j,a)) i := by
  change (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)).mulVec (WithLp.ofLp u) (i,a) = _
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

theorem potential_intertwines (n : ℕ) (h : ℝ) (K : Mat 2) (v : E 2) :
    op (potential n K) (liftCLM n h v) = liftCLM n h (operatorOf K v) := by
  ext p
  rcases p with ⟨i,a⟩
  rw [potential_apply]
  change (∑ b : Fin 2, K a b * (phase ((i.val : ℝ)*h) * v b)) =
    phase ((i.val : ℝ)*h) * (K.mulVec (WithLp.ofLp v) a)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem laplacian_lift (n : ℕ) (h : ℝ)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2)) (liftCLM n h v) =
      (spatialSymbol h : ℂ) • liftCLM n h v := by
  ext p
  rcases p with ⟨i,a⟩
  rw [laplacian_apply]
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((j.val : ℝ)*h) * v a) i =
      (spatialSymbol h : ℂ) * (phase ((i.val : ℝ)*h) * v a)
  have hf : Function.Periodic (fun x => phase x * v a) (2*Real.pi) := by
    intro x
    change phase (x + 2 * Real.pi) * v a = phase x * v a
    rw [phase_periodic x]
  have hs := PeriodicGrid.matrix_sample_stencil (n := n) (2*Real.pi) h
    (fun x => phase x * v a) hf hmesh i
  change (PeriodicGrid.laplacian n h).mulVec
    (fun j => phase ((j.val : ℝ)*h) * v a) i = _ at hs
  rw [hs]
  have hc := phase_centeredStencil h ((i.val : ℝ)*h)
  unfold centeredStencil at hc
  calc
    _ = ((2*phase ((i.val : ℝ)*h) - phase ((i.val : ℝ)*h+h) -
      phase ((i.val : ℝ)*h-h))/(h : ℂ)^2) * v a := by ring
    _ = _ := by rw [hc]; ring

theorem hamiltonian_intertwines (n : ℕ) (h : ℝ) (K : Mat 2)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    op (hamiltonian n h K) (liftCLM n h v) =
      liftCLM n h (operatorOf ((spatialSymbol h : ℂ) • 1 + K) v) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, laplacian_lift n h hmesh,
    potential_intertwines, operatorOf, map_smul, map_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]

theorem scalar_add_isHermitian (lambda : ℝ) (K : Mat 2) (hK : K.IsHermitian) :
    ((lambda : ℂ) • (1 : Mat 2) + K).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hK.eq]

theorem hamiltonian_step_lift (n : ℕ) (h a : ℝ) (K : Mat 2) (hK : K.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    step a (hamiltonian n h K) (liftCLM n h v) =
      liftCLM n h (Chat ((spatialSymbol h : ℂ) • 1 + K) a v) := by
  exact step_intertwines (liftCLM n h) (hamiltonian n h K) _
    (hamiltonian_isHermitian n h K hK) (scalar_add_isHermitian _ K hK)
    (hamiltonian_intertwines n h K hmesh) a v

theorem potential_step_lift (n : ℕ) (h a : ℝ) (K : Mat 2) (hK : K.IsHermitian)
    (v : E 2) :
    step a (potential n K) (liftCLM n h v) = liftCLM n h (Chat K a v) := by
  exact step_intertwines (liftCLM n h) (potential n K) K
    (potential_isHermitian n K hK) hK (potential_intertwines n h K) a v

def symmetric (n : ℕ) (h k : ℝ) (K Q : Mat 2) : Vec (Grid n) →L[ℂ] Vec (Grid n) :=
  step (k / 4) (hamiltonian n h K) * step (k / 2) (potential n Q) *
    step (k / 4) (hamiltonian n h K)

theorem symmetric_mem_unitary (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) :
    symmetric n h k K Q ∈ unitary (Vec (Grid n) →L[ℂ] Vec (Grid n)) := by
  exact (unitary _).mul_mem ((unitary _).mul_mem
    (step_mem_unitary _ _ (hamiltonian_isHermitian n h K hK))
    (step_mem_unitary _ _ (potential_isHermitian n Q hQ)))
    (step_mem_unitary _ _ (hamiltonian_isHermitian n h K hK))

theorem symmetric_pow_norm (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) (N : ℕ) (u : Vec (Grid n)) :
    ‖(symmetric n h k K Q ^ N) u‖ = ‖u‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    ((unitary _).pow_mem (symmetric_mem_unitary n h k K Q hK hQ) N) u

theorem symmetric_lift (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (v : E 2) :
    symmetric n h k K Q (liftCLM n h v) =
      liftCLM n h (symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k v) := by
  simp only [symmetric, symmetricStepHat, ContinuousLinearMap.mul_apply,
    hamiltonian_step_lift n h _ K hK hmesh, potential_step_lift n h _ Q hQ]

theorem symmetric_pow_lift (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (v : E 2) :
    (symmetric n h k K Q ^ N) (liftCLM n h v) =
      liftCLM n h ((symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k ^ N) v) := by
  induction N generalizing v with
  | zero => simp
  | succ N ih =>
    simp only [pow_succ, ContinuousLinearMap.mul_apply,
      symmetric_lift n h k K Q hK hQ hmesh, ih]

/-- Exact conversion of full-grid error into the bounded two-component error. -/
theorem symmetric_pow_weighted_error (n : ℕ) (h k : ℝ) (K Q : Mat 2)
    (hK : K.IsHermitian) (hQ : Q.IsHermitian) (hh : 0 ≤ h)
    (hmesh : ((n + 1 : ℕ) : ℝ) * h = 2 * Real.pi) (N : ℕ) (u v : E 2) :
    Real.sqrt h * ‖(symmetric n h k K Q ^ N) (liftCLM n h u) - liftCLM n h v‖ =
      Real.sqrt (2*Real.pi) *
        ‖(symmetricStepHat ((spatialSymbol h : ℂ) • 1 + K) Q k ^ N) u - v‖ := by
  rw [symmetric_pow_lift n h k K Q hK hQ hmesh, ← map_sub]
  exact lift_weighted_norm n h hh hmesh _

theorem hamiltonian_apply_stencil (n : ℕ) (h : ℝ) (K : Mat 2)
    (u : Vec (Grid n)) (i : Fin (n + 1)) (a : Fin 2) :
    op (hamiltonian n h K) u (i,a) =
      (2*u (i,a) - u (PeriodicGrid.next i,a) - u (PeriodicGrid.prev i,a))/(h : ℂ)^2 +
        ∑ b : Fin 2, K a b * u (i,b) := by
  simp only [hamiltonian, map_add, ContinuousLinearMap.add_apply, PiLp.add_apply,
    laplacian_apply, potential_apply, PeriodicGrid.laplacian_mulVec]

theorem hamiltonian_mul_potential (n : ℕ) (h : ℝ) (K Q : Mat 2) :
    hamiltonian n h K * potential n Q =
      PeriodicGrid.laplacian n h ⊗ₖ Q + potential n (K * Q) := by
  simp [hamiltonian, potential, Matrix.add_mul, ← Matrix.mul_kronecker_mul]

theorem potential_mul_hamiltonian (n : ℕ) (h : ℝ) (K Q : Mat 2) :
    potential n Q * hamiltonian n h K =
      PeriodicGrid.laplacian n h ⊗ₖ Q + potential n (Q * K) := by
  simp [hamiltonian, potential, Matrix.mul_add, ← Matrix.mul_kronecker_mul]

/-- Noncommuting internal components remain noncommuting on every full grid. -/
theorem hamiltonian_noncommutes_potential (n : ℕ) (h : ℝ) (K Q : Mat 2)
    (hKQ : ¬ Commute K Q) : ¬ Commute (hamiltonian n h K) (potential n Q) := by
  intro hc
  apply hKQ
  change K * Q = Q * K
  ext a b
  have he := congrArg (fun M : Matrix (Grid n) (Grid n) ℂ =>
    M ((0 : Fin (n + 1)),a) ((0 : Fin (n + 1)),b)) hc.eq
  rw [hamiltonian_mul_potential, potential_mul_hamiltonian] at he
  simp only [potential, Matrix.add_apply, Matrix.kronecker_apply,
    Matrix.one_apply_eq, one_mul] at he
  exact add_left_cancel he

#print axioms stage_unique
#print axioms den_intertwines
#print axioms num_intertwines
#print axioms step_intertwines
#print axioms lift_norm_sq
#print axioms lift_weighted_norm
#print axioms step_mem_unitary
#print axioms potential_isHermitian
#print axioms hamiltonian_isHermitian
#print axioms potential_intertwines
#print axioms laplacian_lift
#print axioms hamiltonian_intertwines
#print axioms hamiltonian_step_lift
#print axioms potential_step_lift
#print axioms symmetric_mem_unitary
#print axioms symmetric_pow_norm
#print axioms symmetric_lift
#print axioms symmetric_pow_lift
#print axioms symmetric_pow_weighted_error
#print axioms hamiltonian_apply_stencil
#print axioms hamiltonian_noncommutes_potential

end NDEAEvolve.Exp007.SpinorGrid
