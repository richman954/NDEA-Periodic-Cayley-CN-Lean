import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.NoncommRing

open scoped ComplexConjugate Matrix ComplexOrder
open Matrix

#check Matrix.IsHermitian
#check Matrix.IsHermitian.isSelfAdjoint
#check IsSelfAdjoint.star_eq
#check IsSelfAdjoint.smul
#check IsSelfAdjoint.smul_mem_skewAdjoint
#check IsSkewAdjoint
#check Matrix.star_eq_conjTranspose
#check Matrix.posSemidef_conjTranspose_mul_self
#check Matrix.PosDef.one
#check Matrix.PosDef.add_posSemidef
#check Matrix.PosDef.isUnit
#check IsUnit.mul_iff
#check IsUnit.star
#check IsUnit.unit
#check IsUnit.unit_spec
#check Units.mul_inv_mem_unitary
#check Unitary.mem_iff
#check Matrix.mem_unitaryGroup_iff
#check Matrix.mem_unitaryGroup_iff'
#check ContinuousLinearMap.isUnit_iff_bijective
#check LinearMap.injective_iff_surjective
#check ContinuousLinearMap.norm_map_of_mem_unitary
#check ContinuousLinearMap.inner_map_map_of_mem_unitary
#check Complex.star_def
#check Complex.conj_I
#check star_smul
#check star_add

example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (τ : ℝ) :
    IsSkewAdjoint (((τ : ℂ) * Complex.I) • A) := by
  rw [isSkewAdjoint_iff]
  ext i j
  simp [Matrix.star_eq_conjTranspose, hA.apply, mul_comm]
