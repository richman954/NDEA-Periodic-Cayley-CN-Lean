import KineticSymbolBound
import SampledPotentialBounds

noncomputable section
open scoped Matrix Kronecker
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp006
open NDEAEvolve.Exp007.SpinorGrid
namespace NDEAEvolve.Exp016

/- The fixed Z factor is bounded directly from the existing block norm
   lemma.  This keeps the actual split operator visible: no commuting or
   scalar surrogate is introduced. -/
theorem sampledPotentialZ_opNorm_le_one (n : ℕ) (h : ℝ) :
    ‖op (potential n Exp007.Z)‖ ≤ 1 := by
  rw [← sampledBlock_const n h Exp007.Z]
  apply sampledBlock_opNorm_le n h (fun _ => Exp007.Z) 1 (by positivity)
  intro i
  simpa using Exp007.Z_opNorm_le_one

theorem sampledSplitA_opNorm_le (M : ℕ) (h : ℝ) (hh : 0 < h) :
    ‖op (sampledSplitA (2 * M) h)‖ ≤ 4 / h ^ 2 + 1 := by
  rw [sampledSplitA, hamiltonian]
  simp only [map_add]
  change ‖op (gridKinetic (2 * M) h) +
      op (potential (2 * M) Exp007.Z)‖ ≤ 4 / h ^ 2 + 1
  calc
    ‖op (gridKinetic (2 * M) h) + op (potential (2 * M) Exp007.Z)‖ ≤
        ‖op (gridKinetic (2 * M) h)‖ + ‖op (potential (2 * M) Exp007.Z)‖ :=
      norm_add_le _ _
    _ ≤ 4 / h ^ 2 + 1 :=
      add_le_add (gridKinetic_opNorm_le M h hh) (sampledPotentialZ_opNorm_le_one (2 * M) h)

#print axioms sampledPotentialZ_opNorm_le_one
#print axioms sampledSplitA_opNorm_le
end NDEAEvolve.Exp016
