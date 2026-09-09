import WeightedTail

/-! A summable second weighted Fourier moment bounds every derivative needed
for the classical periodic spinor equation. -/
noncomputable section
open scoped BigOperators
open NDEAEvolve.Exp002 NDEAEvolve.Exp003 NDEAEvolve.Exp008 NDEAEvolve.Exp009
namespace NDEAEvolve.Exp010

def Regular (a : ℤ → E 2) : Prop :=
  Summable fun m => frequencyWeight 2 m * ‖a m‖

def modeTime (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (-Complex.I) • operatorOf (modeGenerator m) (modeSolution m v t x)

def modeSpace (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (Complex.I*(m:ℂ)) • modeSolution m v t x

def modeSecond (m : ℤ) (v : E 2) (t x : ℝ) : E 2 :=
  (-((m:ℂ)^2)) • modeSolution m v t x

theorem regular_absolute (a : ℤ → E 2) (ha : Regular a) :
    Summable fun m => ‖a m‖ := weighted_summable_implies_absolute 2 a ha

theorem frequencyWeight_two_pos (m : ℤ) : 0 < frequencyWeight 2 m :=
  lt_of_lt_of_le (by norm_num) (frequencyWeight_one_le 2 m)

theorem frequency_abs_le_weight (m : ℤ) : |(m:ℝ)| ≤ frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_nonneg |(m:ℝ)|]

theorem frequency_sq_le_weight (m : ℤ) : (m:ℝ)^2 ≤ frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_abs (m:ℝ)]

theorem frequency_generator_le_weight (m : ℤ) :
    (m:ℝ)^2+2 ≤ 2*frequencyWeight 2 m := by
  unfold frequencyWeight
  nlinarith [abs_nonneg (m:ℝ), sq_abs (m:ℝ), sq_nonneg (m:ℝ)]

theorem modeGenerator_norm_le (m : ℤ) : ‖operatorOf (modeGenerator m)‖ ≤ (m:ℝ)^2+2 := by
  calc
    _ ≤ ‖operatorOf (Exp007.A ((m:ℝ)^2))‖+‖operatorOf Exp007.B‖ := by
      simpa only [modeGenerator, operatorOf, map_add] using
        norm_add_le (operatorOf (Exp007.A ((m:ℝ)^2))) (operatorOf Exp007.B)
    _ ≤ ((m:ℝ)^2+1)+1 := add_le_add
      (A_opNorm_le ((m:ℝ)^2) (sq_nonneg _)) Exp007.B_opNorm_le_one
    _ = _ := by ring

theorem complex_integer_norm (m : ℤ) : ‖(m:ℂ)‖ = |(m:ℝ)| := by
  have he : (m:ℂ)=((m:ℝ):ℂ) := by simp
  rw [he, Complex.norm_real, Real.norm_eq_abs]

theorem modeTime_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeTime m v t x‖ ≤ 2*frequencyWeight 2 m*‖v‖ := by
  unfold modeTime
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖operatorOf (modeGenerator m)‖*‖modeSolution m v t x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((m:ℝ)^2+2)*‖v‖ := by
      rw [modeSolution_norm]
      exact mul_le_mul_of_nonneg_right (modeGenerator_norm_le m) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (frequency_generator_le_weight m) (norm_nonneg _)

theorem modeSpace_norm_eq (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSpace m v t x‖ = |(m:ℝ)| * ‖v‖ := by
  simp only [modeSpace, norm_smul, norm_mul, Complex.norm_I, one_mul,
    complex_integer_norm, modeSolution_norm]

theorem modeSecond_norm_eq (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSecond m v t x‖ = (m:ℝ)^2*‖v‖ := by
  simp only [modeSecond, norm_smul, norm_neg, norm_pow, complex_integer_norm,
    sq_abs, modeSolution_norm]

theorem modeSpace_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSpace m v t x‖ ≤ frequencyWeight 2 m*‖v‖ := by
  rw [modeSpace_norm_eq]
  exact mul_le_mul_of_nonneg_right (frequency_abs_le_weight m) (norm_nonneg _)

theorem modeSecond_norm_le (m : ℤ) (v : E 2) (t x : ℝ) :
    ‖modeSecond m v t x‖ ≤ frequencyWeight 2 m*‖v‖ := by
  rw [modeSecond_norm_eq]
  exact mul_le_mul_of_nonneg_right (frequency_sq_le_weight m) (norm_nonneg _)

theorem regular_time_majorant (a : ℤ → E 2) (ha : Regular a) :
    Summable fun m => 2*frequencyWeight 2 m*‖a m‖ := by
  simpa only [mul_assoc] using ha.mul_left 2

theorem regular_time_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeTime m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeTime_norm_le m (a m) t x) (regular_time_majorant a ha)

theorem regular_space_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeSpace m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeSpace_norm_le m (a m) t x) ha

theorem regular_second_summable_norm (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => ‖modeSecond m (a m) t x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => modeSecond_norm_le m (a m) t x) ha

theorem regular_time_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeTime m (a m) t x := (regular_time_summable_norm a ha t x).of_norm

theorem regular_space_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeSpace m (a m) t x := (regular_space_summable_norm a ha t x).of_norm

theorem regular_second_summable (a : ℤ → E 2) (ha : Regular a) (t x : ℝ) :
    Summable fun m => modeSecond m (a m) t x := (regular_second_summable_norm a ha t x).of_norm

end NDEAEvolve.Exp010
