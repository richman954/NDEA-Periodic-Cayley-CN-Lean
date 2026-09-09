import SampledCayleyCertificate

/-! Dimension-independent bounds for the actual sampled block operator.
All matrix sizes use the induced Euclidean operator norm. The proof sums
node norm squares before taking square roots, preserving the constant one.
No regularity or Hermitian assumption is needed for the block norm lemma. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006 NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

/-- The existing full grid Euclidean norm is the sum of its node norm squares. -/
theorem grid_norm_sq_eq_sum_nodeValue (n : ℕ) (y : Vec (Grid n)) :
    ‖y‖ ^ 2 = ∑ i : Fin (n + 1), ‖Exp011.nodeValue n y i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Exp011.nodeValue,
    Fintype.sum_prod_type]

theorem sampledBlock_apply_norm_le (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ i : Fin (n + 1), ‖operatorOf (W ((i.val : ℝ) * h))‖ ≤ C)
    (y : Vec (Grid n)) : ‖op (sampledBlock n h W) y‖ ≤ C * ‖y‖ := by
  have hs : ‖op (sampledBlock n h W) y‖ ^ 2 ≤ (C * ‖y‖) ^ 2 := by
    rw [grid_norm_sq_eq_sum_nodeValue, mul_pow, grid_norm_sq_eq_sum_nodeValue,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [sampledBlock_nodeValue]
    have hi := (operatorOf (W ((i.val : ℝ) * h))).le_of_opNorm_le (hW i)
      (Exp011.nodeValue n y i)
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hi
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs

theorem sampledBlock_opNorm_le (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ i : Fin (n + 1), ‖operatorOf (W ((i.val : ℝ) * h))‖ ≤ C) :
    ‖op (sampledBlock n h W)‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (sampledBlock_apply_norm_le n h W C hC hW)

/-- The fixed Z offset cancels exactly when two sampled potentials are compared. -/
theorem sampledSplitB_sub (n : ℕ) (h : ℝ) (W U : ℝ → Mat 2) :
    sampledSplitB n h W - sampledSplitB n h U =
      sampledBlock n h (fun x => W x - U x) := by
  simp only [sampledSplitB, sampledBlock_sub, sampledBlock_const]
  abel

theorem sampledSplitB_sub_opNorm_le (n : ℕ) (h : ℝ) (W U : ℝ → Mat 2)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hWU : ∀ i : Fin (n + 1), ‖operatorOf (W ((i.val : ℝ) * h) -
      U ((i.val : ℝ) * h))‖ ≤ δ) :
    ‖op (sampledSplitB n h W - sampledSplitB n h U)‖ ≤ δ := by
  rw [sampledSplitB_sub]
  exact sampledBlock_opNorm_le n h _ δ hδ hWU

/-- The actual split potential has norm at most the nodal potential bound plus one. -/
theorem sampledSplitB_opNorm_le (n : ℕ) (h : ℝ) (W : ℝ → Mat 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ i : Fin (n + 1), ‖operatorOf (W ((i.val : ℝ) * h))‖ ≤ C) :
    ‖op (sampledSplitB n h W)‖ ≤ C + 1 := by
  apply sampledBlock_opNorm_le n h _ (C + 1) (by positivity)
  intro i
  change ‖operatorOf (W ((i.val : ℝ) * h) - Exp007.Z)‖ ≤ _
  simp only [operatorOf, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hW i) Exp007.Z_opNorm_le_one)

theorem sampled_operatorPotential_opNorm_le (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) :
    ‖op (sampledBlock n h (operatorPotentialMatrix v))‖ ≤ ∑' j : ℤ, ‖v j‖ := by
  apply sampledBlock_opNorm_le n h _ _ (tsum_nonneg fun _ => norm_nonneg _)
  intro i
  rw [operatorPotentialMatrix_represents]
  exact Exp014.operatorPotential_norm_le v hv _

theorem sampled_operatorPotential_splitB_opNorm_le (n : ℕ) (h : ℝ)
    (v : ℤ → E 2 →L[ℂ] E 2) (hv : Exp014.RegularPotential v) :
    ‖op (sampledSplitB n h (operatorPotentialMatrix v))‖ ≤
      (∑' j : ℤ, ‖v j‖) + 1 := by
  apply sampledSplitB_opNorm_le n h _ _ (tsum_nonneg fun _ => norm_nonneg _)
  intro i
  rw [operatorPotentialMatrix_represents]
  exact Exp014.operatorPotential_norm_le v hv _

#print axioms grid_norm_sq_eq_sum_nodeValue
#print axioms sampledBlock_apply_norm_le
#print axioms sampledBlock_opNorm_le
#print axioms sampledSplitB_sub
#print axioms sampledSplitB_sub_opNorm_le
#print axioms sampledSplitB_opNorm_le
#print axioms sampled_operatorPotential_opNorm_le
#print axioms sampled_operatorPotential_splitB_opNorm_le
end NDEAEvolve.Exp016
