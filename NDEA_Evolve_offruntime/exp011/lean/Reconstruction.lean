import SolutionLipschitz
import ClassicalClosure
import Mathlib.Algebra.Order.Floor.Semiring

/-! Explicit piecewise constant reconstruction of the actual full-grid Cayley
iteration. Space and time indices are clamped to existing nodes/steps. The
right spatial endpoint uses the last grid node, within one cell of the endpoint.
No convergence or reconstruction estimate is assumed in these definitions. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003
open NDEAEvolve.Exp007.SpinorGrid
open NDEAEvolve.Exp008 NDEAEvolve.Exp009 NDEAEvolve.Exp010
namespace NDEAEvolve.Exp011

def nodeValue (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) : E 2 :=
  WithLp.toLp 2 (fun b => v (j,b))

theorem nodeValue_sub (n : ℕ) (v w : Vec (Grid n)) (j : Fin (n+1)) :
    nodeValue n (v-w) j = nodeValue n v j-nodeValue n w j := by
  ext b
  rfl

theorem nodeValue_sampleSolution (n : ℕ) (h : ℝ) (u : ℝ → ℝ → E 2)
    (t : ℝ) (j : Fin (n+1)) :
    nodeValue n (sampleSolution n h u t) j = u t ((j.val:ℝ)*h) := by
  ext b
  rfl

theorem nodeValue_norm_le (n : ℕ) (v : Vec (Grid n)) (j : Fin (n+1)) :
    ‖nodeValue n v j‖ ≤ ‖v‖ := by
  have hs : ‖nodeValue n v j‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [nodeValue, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    have hnonneg (i : Fin (n+1)) : 0≤∑ b : Fin 2, ‖v (i,b)‖^2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg ‖v (i,b)‖
    exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j)
  nlinarith [norm_nonneg (nodeValue n v j), norm_nonneg v]

def spaceIndex (n : ℕ) (h x : ℝ) : Fin (n+1) :=
  ⟨min ⌊x/h⌋₊ n, lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self n)⟩

theorem spaceIndex_distance (n : ℕ) (h x : ℝ) (hh : 0<h)
    (hx : 0≤x) (hL : x≤((n+1:ℕ):ℝ)*h) :
    0≤x-(spaceIndex n h x).val*h ∧ x-(spaceIndex n h x).val*h≤h := by
  have hfloor := Nat.floor_le (div_nonneg hx hh.le)
  have hleft : ((min ⌊x/h⌋₊ n : ℕ):ℝ)≤x/h :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans hfloor
  have hleft' := (le_div_iff₀ hh).mp hleft
  constructor
  · change 0≤x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h
    linarith
  · change x-((min ⌊x/h⌋₊ n : ℕ):ℝ)*h≤h
    by_cases hf : ⌊x/h⌋₊≤n
    · rw [min_eq_left hf]
      have hr := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x/h))
      nlinarith
    · rw [min_eq_right (le_of_not_ge hf)]
      push_cast at hL
      nlinarith

def timeIndex (N : ℕ) (k t : ℝ) : ℕ := min ⌊t/k⌋₊ N

theorem timeIndex_le (N : ℕ) (k t : ℝ) : timeIndex N k t≤N :=
  min_le_right _ _

theorem timeIndex_distance (N : ℕ) (k t : ℝ) (hk : 0<k)
    (ht : 0≤t) (hT : t≤(N:ℝ)*k) :
    0≤t-(timeIndex N k t:ℝ)*k ∧ t-(timeIndex N k t:ℝ)*k≤k := by
  have hT' : t≤((N+1:ℕ):ℝ)*k := by
    push_cast
    nlinarith
  exact spaceIndex_distance N k t hk ht hT'

def gridState (n : ℕ) (h k : ℝ) (a : ℤ → E 2) (j : ℕ) : Vec (Grid n) :=
  (symmetric n h k Exp007.Z Exp007.X ^ j)
    (sampleSolution n h (infiniteSolution a) 0)

def reconstruction (n : ℕ) (h k : ℝ) (N : ℕ) (a : ℤ → E 2) (t x : ℝ) : E 2 :=
  nodeValue n (gridState n h k a (timeIndex N k t)) (spaceIndex n h x)

theorem gridState_node_error (n : ℕ) (h k : ℝ) (a : ℤ → E 2) (j : ℕ)
    (i : Fin (n+1)) (hh : 0<h) :
    ‖nodeValue n (gridState n h k a j) i-
        infiniteSolution a ((j:ℝ)*k) ((i.val:ℝ)*h)‖ ≤
      classicalGridError n h k j a (sampleSolution n h (infiniteSolution a) 0) /
        Real.sqrt h := by
  have hn := nodeValue_norm_le n (gridState n h k a j-
    sampleSolution n h (infiniteSolution a) ((j:ℝ)*k)) i
  rw [nodeValue_sub, nodeValue_sampleSolution] at hn
  apply (le_div_iff₀ (Real.sqrt_pos.2 hh)).mpr
  simpa only [classicalGridError, gridState, mul_comm] using
    mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg h)

theorem reconstruction_error_bound (n : ℕ) (h k : ℝ) (N : ℕ)
    (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) (hh : 0<h) (hk : 0<k)
    (hx : 0≤x) (hL : x≤((n+1:ℕ):ℝ)*h) (ht : 0≤t) (hT : t≤(N:ℝ)*k) :
    ‖reconstruction n h k N a t x-infiniteSolution a t x‖ ≤
      classicalGridError n h k (timeIndex N k t) a
        (sampleSolution n h (infiniteSolution a) 0) / Real.sqrt h +
          moment 2 a*h+2*moment 2 a*k := by
  let j := timeIndex N k t
  let i := spaceIndex n h x
  let s := (j:ℝ)*k
  let y := (i.val:ℝ)*h
  have hdx : |y-x|≤h := by
    have hd := spaceIndex_distance n h x hh hx hL
    rw [abs_sub_comm, abs_of_nonneg hd.1]
    exact hd.2
  have hdt : |s-t|≤k := by
    have hd := timeIndex_distance N k t hk ht hT
    rw [abs_sub_comm, abs_of_nonneg hd.1]
    exact hd.2
  have hs := (solution_space_lipschitz a ha s x y).trans
    (mul_le_mul_of_nonneg_left hdx (moment_nonneg 2 a))
  have ht' := (solution_time_lipschitz a ha x t s).trans
    (mul_le_mul_of_nonneg_left hdt
      (mul_nonneg (by norm_num : (0:ℝ)≤2) (moment_nonneg 2 a)))
  have hn := gridState_node_error n h k a j i hh
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (reconstruction n h k N a t x) (infiniteSolution a s y) (infiniteSolution a t x)
  have hmiddle := norm_sub_le_norm_sub_add_norm_sub
    (infiniteSolution a s y) (infiniteSolution a s x) (infiniteSolution a t x)
  change ‖reconstruction n h k N a t x-infiniteSolution a s y‖≤_ at hn
  have htotal := htriangle.trans (add_le_add hn (hmiddle.trans (add_le_add hs ht')))
  simpa only [add_assoc] using htotal

end NDEAEvolve.Exp011
