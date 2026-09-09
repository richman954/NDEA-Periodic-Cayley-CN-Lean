import Reconstruction

/-! A position-dependent matrix potential on the existing spinor grid.
The split retains the old A = L_h + Z factor and uses B = W_sample - Z.
All identities are exact for arbitrary sampled matrix fields. -/
noncomputable section
open scoped BigOperators Matrix Kronecker
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid

namespace NDEAEvolve.Exp016

def sampledBlock (n : ℕ) (h : ℝ) (W : ℝ → Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  fun p q => if p.1 = q.1 then W ((q.1.val : ℝ) * h) p.2 q.2 else 0

theorem sampledBlock_isHermitian (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (hW : ∀ x, (W x).IsHermitian) : (sampledBlock n h W).IsHermitian := by
  change (sampledBlock n h W).conjTranspose = sampledBlock n h W
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    have he := congrArg (fun K : Mat 2 => K a b) (hW ((i.val : ℝ) * h)).eq
    simpa [Matrix.conjTranspose_apply, sampledBlock] using he
  · simp [Matrix.conjTranspose_apply, sampledBlock, hij, Ne.symm hij]

theorem sampledBlock_apply (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (u : Vec (Grid n)) (i : Fin (n + 1)) (a : Fin 2) :
    op (sampledBlock n h W) u (i, a) =
      ∑ b : Fin 2, W ((i.val : ℝ) * h) a b * u (i, b) := by
  change (sampledBlock n h W).mulVec (WithLp.ofLp u) (i, a) = _
  simp [sampledBlock, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem sampledBlock_nodeValue (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (u : Vec (Grid n)) (i : Fin (n + 1)) :
    Exp011.nodeValue n (op (sampledBlock n h W) u) i =
      operatorOf (W ((i.val : ℝ) * h)) (Exp011.nodeValue n u i) := by
  ext a
  change op (sampledBlock n h W) u (i, a) =
    ∑ b : Fin 2, W ((i.val : ℝ) * h) a b * u (i, b)
  exact sampledBlock_apply n h W u i a

theorem sampledBlock_const (n : ℕ) (h : ℝ) (K : Mat 2) :
    sampledBlock n h (fun _ => K) = potential n K := by
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  by_cases hij : i = j <;>
    simp [sampledBlock, potential, Matrix.kronecker_apply, Matrix.one_apply, hij]

theorem sampledBlock_sub (n : ℕ) (h : ℝ) (W U : ℝ → Mat 2) :
    sampledBlock n h (fun x => W x - U x) = sampledBlock n h W - sampledBlock n h U := by
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  by_cases hij : i = j <;> simp [sampledBlock, hij]

def sampledSplitA (n : ℕ) (h : ℝ) : Matrix (Grid n) (Grid n) ℂ :=
  hamiltonian n h Exp007.Z

def sampledSplitB (n : ℕ) (h : ℝ) (W : ℝ → Mat 2) : Matrix (Grid n) (Grid n) ℂ :=
  sampledBlock n h (fun x => W x - Exp007.Z)

theorem sampledSplitA_isHermitian (n : ℕ) (h : ℝ) :
    (sampledSplitA n h).IsHermitian :=
  hamiltonian_isHermitian n h Exp007.Z Exp007.Z_isHermitian

theorem sampledSplitB_isHermitian (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (hW : ∀ x, (W x).IsHermitian) : (sampledSplitB n h W).IsHermitian :=
  sampledBlock_isHermitian n h _ (fun x => (hW x).sub Exp007.Z_isHermitian)

theorem sampledSplit_sum (n : ℕ) (h : ℝ) (W : ℝ → Mat 2) :
    sampledSplitA n h + sampledSplitB n h W =
      PeriodicGrid.laplacian n h ⊗ₖ (1 : Mat 2) + sampledBlock n h W := by
  rw [sampledSplitA, sampledSplitB, sampledBlock_sub, sampledBlock_const, hamiltonian]
  abel

theorem sampledSplitB_old_constant (n : ℕ) (h : ℝ) :
    sampledSplitB n h (fun _ => Exp007.Z + Exp007.X) = potential n Exp007.X := by
  have he : (fun _ : ℝ => Exp007.Z + Exp007.X - Exp007.Z) = fun _ => Exp007.X := by
    funext x
    abel
  rw [sampledSplitB, he, sampledBlock_const]

#print axioms sampledBlock_isHermitian
#print axioms sampledBlock_apply
#print axioms sampledBlock_nodeValue
#print axioms sampledBlock_const
#print axioms sampledBlock_sub
#print axioms sampledSplitA_isHermitian
#print axioms sampledSplitB_isHermitian
#print axioms sampledSplit_sum
#print axioms sampledSplitB_old_constant
end NDEAEvolve.Exp016
