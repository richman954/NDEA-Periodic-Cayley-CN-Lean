import NDEAMathlibGate.PeriodicLaplacian1DV1R2_ExplicitSBP
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Production V1: periodic grid sampling and centered-stencil bridge. -/

noncomputable section

open Complex
open Set
open scoped BigOperators

namespace NDEAPeriodicSamplingBridgeProbe

namespace Shift

abbrev nextIdx {n : Nat} (i : Fin n) : Fin n :=
  NDEAMathlibGate.PeriodicShift1DV1.nextIdx i
abbrev prevIdx {n : Nat} (i : Fin n) : Fin n :=
  NDEAMathlibGate.PeriodicShift1DV1.prevIdx i
abbrev nextPerm (n : Nat) : Equiv.Perm (Fin n) :=
  NDEAMathlibGate.PeriodicShift1DV1.nextPerm n
abbrev prevPerm (n : Nat) : Equiv.Perm (Fin n) :=
  NDEAMathlibGate.PeriodicShift1DV1.prevPerm n

end Shift

def meshWidth (L : ℝ) (n : ℕ) : ℝ :=
  L / (n : ℝ)

def gridPoint (L : ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  (i.val : ℝ) * meshWidth L n

def sampleFixedPeriod (L : ℝ) (n : ℕ) (u : ℝ → ℂ) : Fin n → ℂ :=
  fun i => u (gridPoint L n i)

@[simp] theorem sampleFixedPeriod_apply
    (L : ℝ) (n : ℕ) (u : ℝ → ℂ) (i : Fin n) :
    sampleFixedPeriod L n u i = u (gridPoint L n i) := by
  rfl

theorem meshWidth_pos_succ
    (L : ℝ) (m : ℕ) (hL : 0 < L) :
    0 < meshWidth L (m + 1) := by
  exact div_pos hL (by positivity)

theorem card_mul_meshWidth_succ (L : ℝ) (m : ℕ) :
    (((m + 1 : ℕ) : ℝ)) * meshWidth L (m + 1) = L := by
  unfold meshWidth
  have hne : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hne]

private theorem nextIdx_val_of_ne_last
    {m : ℕ} (i : Fin (m + 1)) (hi : i ≠ Fin.last m) :
    (Shift.nextIdx i).val = i.val + 1 := by
  change (finRotate (m + 1) i).val = i.val + 1
  exact coe_finRotate_of_ne_last hi

private theorem prevIdx_val_of_ne_zero
    {m : ℕ} (i : Fin (m + 1)) (hi : i ≠ 0) :
    (Shift.prevIdx i).val = i.val - 1 := by
  change ((finRotate (m + 1)).symm i).val = i.val - 1
  exact coe_finRotate_symm_of_ne_zero hi

private theorem nextIdx_last {m : ℕ} :
    Shift.nextIdx (Fin.last m) = (0 : Fin (m + 1)) := by
  change finRotate (m + 1) (Fin.last m) = (0 : Fin (m + 1))
  exact finRotate_last

private theorem prevIdx_zero {m : ℕ} :
    Shift.prevIdx (0 : Fin (m + 1)) = Fin.last m := by
  change NDEAMathlibGate.PeriodicShift1DV1.prevIdx
    (0 : Fin (m + 1)) = Fin.last m
  have h := NDEAMathlibGate.PeriodicShift1DV1.prevIdx_nextIdx (Fin.last m)
  unfold NDEAMathlibGate.PeriodicShift1DV1.prevIdx
    NDEAMathlibGate.PeriodicShift1DV1.prevPerm
    NDEAMathlibGate.PeriodicShift1DV1.nextPerm
  unfold NDEAMathlibGate.PeriodicShift1DV1.prevIdx
    NDEAMathlibGate.PeriodicShift1DV1.prevPerm
    NDEAMathlibGate.PeriodicShift1DV1.nextIdx
    NDEAMathlibGate.PeriodicShift1DV1.nextPerm at h
  rw [finRotate_last] at h
  exact h

theorem sample_next
    (L : ℝ)
    (u : ℝ → ℂ)
    (hu : Function.Periodic u L)
    {m : ℕ}
    (i : Fin (m + 1)) :
    sampleFixedPeriod L (m + 1) u (Shift.nextIdx i) =
      u (gridPoint L (m + 1) i + meshWidth L (m + 1)) := by
  by_cases hi : i = Fin.last m
  · subst i
    rw [nextIdx_last]
    simp only [sampleFixedPeriod, gridPoint, Fin.val_zero, Fin.val_last,
      Nat.cast_zero, zero_mul]
    have hcoord :
        (m : ℝ) * meshWidth L (m + 1) + meshWidth L (m + 1) = L := by
      calc
        (m : ℝ) * meshWidth L (m + 1) + meshWidth L (m + 1) =
            (((m + 1 : ℕ) : ℝ)) * meshWidth L (m + 1) := by
              push_cast
              ring
        _ = L := card_mul_meshWidth_succ L m
    rw [hcoord]
    simpa using (hu 0).symm
  · change
      u (((Shift.nextIdx i).val : ℝ) * meshWidth L (m + 1)) =
        u ((i.val : ℝ) * meshWidth L (m + 1) + meshWidth L (m + 1))
    apply congrArg u
    rw [nextIdx_val_of_ne_last i hi]
    push_cast
    ring

theorem sample_prev
    (L : ℝ)
    (u : ℝ → ℂ)
    (hu : Function.Periodic u L)
    {m : ℕ}
    (i : Fin (m + 1)) :
    sampleFixedPeriod L (m + 1) u (Shift.prevIdx i) =
      u (gridPoint L (m + 1) i - meshWidth L (m + 1)) := by
  by_cases hi : i = 0
  · subst i
    rw [prevIdx_zero]
    simp only [sampleFixedPeriod, gridPoint, Fin.val_zero, Fin.val_last,
      Nat.cast_zero, zero_mul, zero_sub]
    have hcoord :
        -meshWidth L (m + 1) + L = (m : ℝ) * meshWidth L (m + 1) := by
      calc
        -meshWidth L (m + 1) + L =
            -meshWidth L (m + 1) +
              (((m + 1 : ℕ) : ℝ)) * meshWidth L (m + 1) := by
                rw [card_mul_meshWidth_succ L m]
        _ = (m : ℝ) * meshWidth L (m + 1) := by
          push_cast
          ring
    calc
      u ((m : ℝ) * meshWidth L (m + 1)) =
          u (-meshWidth L (m + 1) + L) := by rw [hcoord]
      _ = u (-meshWidth L (m + 1)) := hu (-meshWidth L (m + 1))
  · change
      u (((Shift.prevIdx i).val : ℝ) * meshWidth L (m + 1)) =
        u ((i.val : ℝ) * meshWidth L (m + 1) - meshWidth L (m + 1))
    apply congrArg u
    have hival : i.val ≠ 0 := by
      intro hzero
      apply hi
      apply Fin.ext
      simpa using hzero
    have hone : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hival
    rw [prevIdx_val_of_ne_zero i hi]
    rw [Nat.cast_sub hone]
    ring

theorem periodicNegLaplacian_sample_apply
    (L : ℝ)
    (u : ℝ → ℂ)
    (hu : Function.Periodic u L)
    {m : ℕ}
    (i : Fin (m + 1)) :
    (NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian
      (meshWidth L (m + 1)) (m + 1)).mulVec
      (sampleFixedPeriod L (m + 1) u) i =
    (2 * u (gridPoint L (m + 1) i) -
        u (gridPoint L (m + 1) i + meshWidth L (m + 1)) -
        u (gridPoint L (m + 1) i - meshWidth L (m + 1))) /
      (meshWidth L (m + 1) : ℂ) ^ 2 := by
  rw [NDEAMathlibGate.PeriodicLaplacian1DV1R.periodicNegLaplacian_mulVec_apply_total]
  change
    (2 * u (gridPoint L (m + 1) i) -
        sampleFixedPeriod L (m + 1) u (Shift.nextIdx i) -
        sampleFixedPeriod L (m + 1) u (Shift.prevIdx i)) /
      (meshWidth L (m + 1) : ℂ) ^ 2 = _
  rw [sample_next L u hu i, sample_prev L u hu i]

#check sample_next
#check sample_prev
#check periodicNegLaplacian_sample_apply
#print axioms sample_next
#print axioms sample_prev
#print axioms periodicNegLaplacian_sample_apply

end NDEAPeriodicSamplingBridgeProbe
