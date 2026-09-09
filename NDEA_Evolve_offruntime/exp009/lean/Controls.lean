import InfiniteReference
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact controls with a coefficient at every signed integer frequency.
The encoded geometric sequence is an independent formal example, not the
two-spinor geometric datum used by the floating-point diagnostic. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009.Controls

def geometricCoefficients (m : ℤ) : E 2 :=
  ((1/2 : ℂ)^Encodable.encode m) • Exp007.Controls.initialSpinor

theorem geometric_coefficient_norm (m : ℤ) :
    ‖geometricCoefficients m‖ = (1/2 : ℝ)^Encodable.encode m := by
  simp [geometricCoefficients, norm_smul, norm_pow, Exp007.Controls.initialSpinor_norm]

theorem geometric_summable_norm : Summable (fun m : ℤ => ‖geometricCoefficients m‖) := by
  simp only [geometric_coefficient_norm]
  exact summable_geometric_two_encode

theorem geometric_coefficient_nonzero (m : ℤ) : geometricCoefficients m ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [geometric_coefficient_norm]
  positivity

theorem geometric_support_all : Function.support geometricCoefficients = Set.univ := by
  ext m
  simp [Function.mem_support, geometric_coefficient_nonzero]

theorem geometric_infinite_support : (Function.support geometricCoefficients).Infinite := by
  rw [geometric_support_all]
  exact Set.infinite_univ

theorem geometric_tail_positive (M : ℕ) : 0 < tail M geometricCoefficients := by
  have hm : (M:ℤ)+1 ∉ band M := by simp [band]
  let j : {m : ℤ // m ∉ band M} := ⟨(M:ℤ)+1, hm⟩
  rw [tail_eq_tsum_compl M geometricCoefficients geometric_summable_norm]
  have hs := geometric_summable_norm.subtype (fun m => m ∉ band M)
  have hp : 0 < ‖geometricCoefficients j‖ := norm_pos_iff.mpr (geometric_coefficient_nonzero _)
  exact hp.trans_le (hs.le_tsum j (fun _ _ => norm_nonneg _))

theorem geometric_tail_tends_to_zero :
    Filter.Tendsto (fun M => tail M geometricCoefficients) Filter.atTop (nhds 0) :=
  tail_tendsto_zero geometricCoefficients geometric_summable_norm

theorem geometric_infinite_reference_summable (t x : ℝ) :
    Summable (fun m => Exp008.modeSolution m (geometricCoefficients m) t x) :=
  modeSolution_summable geometricCoefficients geometric_summable_norm t x

theorem grid_multiple_is_constant_mode (n r : ℕ) (h : ℝ)
    (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) (v : E 2) :
    modeLift n h ((r*(n+1):ℕ):ℤ) v = modeLift n h 0 v := by
  ext p
  simp only [modeLift, WithLp.ofLp_toLp, Int.cast_natCast, Int.cast_zero]
  have hp : Exp006.phase (((r*(n+1):ℕ):ℝ)*((p.1.val:ℝ)*h))=1 := by
    rw [show ((r*(n+1):ℕ):ℝ)*((p.1.val:ℝ)*h) =
      ((r*p.1.val:ℕ):ℝ)*(((n+1:ℕ):ℝ)*h) by push_cast; ring, hmesh]
    simpa using Exp006.phase_periodic.nat_mul_eq (r*p.1.val)
  rw [hp]
  simp

/-- Coherent modes at d and 2d have more sampled energy than the naive l2
formula. Both frequencies are outside every cutoff M<d. -/
theorem coherent_aliases_violate_l2_sampling (n : ℕ) (h : ℝ)
    (hh : 0<h) (hmesh : ((n+1:ℕ):ℝ)*h=2*Real.pi) :
    2*Real.pi*(‖Exp007.Controls.initialSpinor‖^2+‖Exp007.Controls.initialSpinor‖^2) <
      (Real.sqrt h*‖modeLift n h ((1*(n+1):ℕ):ℤ) Exp007.Controls.initialSpinor +
        modeLift n h ((2*(n+1):ℕ):ℤ) Exp007.Controls.initialSpinor‖)^2 := by
  rw [grid_multiple_is_constant_mode n 1 h hmesh,
    grid_multiple_is_constant_mode n 2 h hmesh]
  have hn : ‖modeLift n h 0 Exp007.Controls.initialSpinor +
      modeLift n h 0 Exp007.Controls.initialSpinor‖ =
      2*‖modeLift n h 0 Exp007.Controls.initialSpinor‖ := by
    rw [← two_smul ℂ (modeLift n h 0 Exp007.Controls.initialSpinor), norm_smul]
    norm_num
  have hw := modeLift_weighted_norm n h 0 hh.le hmesh Exp007.Controls.initialSpinor
  rw [Exp007.Controls.initialSpinor_norm, mul_one] at hw
  rw [hn]
  rw [show Real.sqrt h*(2*‖modeLift n h 0 Exp007.Controls.initialSpinor‖) =
    2*(Real.sqrt h*‖modeLift n h 0 Exp007.Controls.initialSpinor‖) by ring, hw]
  rw [Exp007.Controls.initialSpinor_norm]
  nlinarith [Real.sq_sqrt (by positivity : 0≤2*Real.pi), Real.pi_pos]

end NDEAEvolve.Exp009.Controls
