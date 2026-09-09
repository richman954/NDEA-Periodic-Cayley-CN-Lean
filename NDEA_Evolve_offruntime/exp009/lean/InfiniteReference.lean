import SuperpositionClosure
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Infinite absolutely summable Fourier references and an alias-safe sampled tail.
No discrete Parseval identity is asserted for the infinite spectrum. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008
open NDEAEvolve.Exp007.SpinorGrid NDEAEvolve.Exp008.FourierGrid
namespace NDEAEvolve.Exp009

def band (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
def mass (a : ℤ → E 2) : ℝ := ∑' m, ‖a m‖
def tail (M : ℕ) (a : ℤ → E 2) : ℝ :=
  mass a - ∑ m ∈ band M, ‖a m‖
def infiniteSolution (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  ∑' m, modeSolution m (a m) t x
def infiniteGrid (n : ℕ) (h : ℝ) (a : ℤ → E 2) (t : ℝ) : Vec (Grid n) :=
  ∑' m, modeLiftCLM n h m (modeOrbit m t (a m))

theorem band_frequency_bound (M : ℕ) (m : ℤ) (hm : m ∈ band M) :
    |(m : ℝ)| ≤ (M : ℝ) := by
  have h := Finset.mem_Icc.mp hm
  apply abs_le.mpr
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem band_tendsto_atTop :
    Filter.Tendsto band Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro s
  filter_upwards [Filter.eventually_ge_atTop (s.sup Int.natAbs)] with M hM
  intro m hm
  have hn : m.natAbs ≤ M := (Finset.le_sup (f := Int.natAbs) hm).trans hM
  have hab : |m| ≤ (M : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hn
  exact Finset.mem_Icc.mpr (abs_le.mp hab)

theorem mass_nonneg (a : ℤ → E 2) : 0 ≤ mass a :=
  tsum_nonneg fun _ => norm_nonneg _

theorem band_mass_le (M : ℕ) (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    (∑ m ∈ band M, ‖a m‖) ≤ mass a :=
  ha.sum_le_tsum _ (fun _ _ => norm_nonneg _)

theorem tail_nonneg (M : ℕ) (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    0 ≤ tail M a := sub_nonneg.mpr (band_mass_le M a ha)

theorem tail_eq_tsum_compl (M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) :
    tail M a = ∑' m : {m : ℤ // m ∉ band M}, ‖a m‖ := by
  have he := ha.sum_add_tsum_subtype_compl (band M)
  unfold tail mass
  linarith

theorem tail_tendsto_zero (a : ℤ → E 2) (ha : Summable fun m => ‖a m‖) :
    Filter.Tendsto (fun M : ℕ => tail M a) Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto (fun M : ℕ => ∑ m ∈ band M, ‖a m‖)
      Filter.atTop (nhds (mass a)) :=
    ha.hasSum.comp band_tendsto_atTop
  simpa [tail] using (tendsto_const_nhds (x := mass a)).sub hs

theorem coefficientNorm_band_le_mass (M : ℕ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) : coefficientNorm (band M) a ≤ mass a := by
  have hp : coefficientNorm (band M) a ≤ ∑ m ∈ band M, ‖a m‖ := by
    unfold coefficientNorm
    apply (Real.sqrt_le_iff).mpr
    exact ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)⟩
  exact hp.trans (band_mass_le M a ha)

theorem modeSolution_summable_norm (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t x : ℝ) :
    Summable fun m => ‖modeSolution m (a m) t x‖ := by simpa using ha

theorem modeSolution_summable (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t x : ℝ) :
    Summable fun m => modeSolution m (a m) t x :=
  (modeSolution_summable_norm a ha t x).of_norm

theorem infiniteSolution_periodic (a : ℤ → E 2) (t : ℝ) :
    Function.Periodic (infiniteSolution a t) (2 * Real.pi) := by
  intro x
  unfold infiniteSolution
  apply tsum_congr
  intro m
  exact modeSolution_periodic m (a m) t x

theorem infiniteSolution_initial (a : ℤ → E 2) (x : ℝ) :
    infiniteSolution a 0 x = ∑' m : ℤ, Exp006.phase ((m : ℝ) * x) • a m := by
  simp [infiniteSolution]

theorem modeLift_norm (n : ℕ) (h : ℝ) (m : ℤ) (v : E 2) :
    ‖modeLiftCLM n h m v‖ = Real.sqrt ((n+1 : ℕ) : ℝ) * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact modeLift_norm_sq n h m v

theorem infiniteGrid_summable_norm (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) :
    Summable fun m => ‖modeLiftCLM n h m (modeOrbit m t (a m))‖ := by
  simp only [modeLift_norm, modeOrbit_norm]
  exact ha.mul_left _

theorem infiniteGrid_summable (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) :
    Summable fun m => modeLiftCLM n h m (modeOrbit m t (a m)) :=
  (infiniteGrid_summable_norm n h a ha t).of_norm

theorem infiniteGrid_initial (n : ℕ) (h : ℝ) (a : ℤ → E 2) :
    infiniteGrid n h a 0 = ∑' m, modeLiftCLM n h m (a m) := by
  simp [infiniteGrid]

theorem infiniteGrid_is_sampled_solution (n : ℕ) (h : ℝ) (a : ℤ → E 2)
    (ha : Summable fun m => ‖a m‖) (t : ℝ) (p : Grid n) :
    infiniteGrid n h a t p = infiniteSolution a t ((p.1.val : ℝ) * h) p.2 := by
  have hg := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Grid n => ℂ) p).map_tsum
    (infiniteGrid_summable n h a ha t)
  have hs := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) p.2).map_tsum
    (modeSolution_summable a ha t ((p.1.val : ℝ) * h))
  change infiniteGrid n h a t p =
    ∑' m, (modeLiftCLM n h m (modeOrbit m t (a m))) p at hg
  change infiniteSolution a t ((p.1.val : ℝ)*h) p.2 =
    ∑' m, modeSolution m (a m) t ((p.1.val : ℝ)*h) p.2 at hs
  exact hg.trans ((tsum_congr fun _ => rfl).trans hs.symm)

theorem infiniteGrid_tail_bound (M n : ℕ) (h : ℝ) (a : ℤ → E 2) (t : ℝ)
    (ha : Summable fun m => ‖a m‖) (hh : 0 < h)
    (hmesh : ((n+1 : ℕ) : ℝ)*h = 2*Real.pi) :
    Real.sqrt h * ‖infiniteGrid n h a t -
      superpositionLift n h (band M) (fun m => modeOrbit m t (a m))‖ ≤
      Real.sqrt (2*Real.pi)*tail M a := by
  have hs := infiniteGrid_summable n h a ha t
  have hn := infiniteGrid_summable_norm n h a ha t
  unfold infiniteGrid superpositionLift
  rw [← hs.sum_add_tsum_subtype_compl (band M), add_sub_cancel_left]
  have hb := norm_tsum_le_tsum_norm (hn.subtype (fun m => m ∉ band M))
  calc
    _ ≤ Real.sqrt h * (∑' m : {m : ℤ // m ∉ band M},
        ‖modeLiftCLM n h m (modeOrbit m t (a m))‖) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = ∑' m : {m : ℤ // m ∉ band M},
        Real.sqrt (2*Real.pi)*‖a m‖ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      simpa using modeLift_weighted_norm n h m hh.le hmesh (modeOrbit m t (a m))
    _ = _ := by rw [tsum_mul_left, ← tail_eq_tsum_compl M a ha]

end NDEAEvolve.Exp009
