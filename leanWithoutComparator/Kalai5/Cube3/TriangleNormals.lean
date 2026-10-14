import Kalai5.Cube3.PositiveFamilies

/-! Exact outward normals of a triangle. Multiplying by its signed determinant
avoids an orientation case split; the common raw width is the determinant squared. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

structure TriangleData where
  point : Fin 3 → E 2
  det_ne : det2 (point 1-point 0) (point 2-point 0) ≠ 0

namespace TriangleData
variable (T : TriangleData)

noncomputable def determinant : ℝ := det2 (T.point 1-T.point 0) (T.point 2-T.point 0)
noncomputable def raw (i : Fin 3) : E 2 := T.determinant •
  (![normal2 (T.point 1-T.point 2),normal2 (T.point 2-T.point 0),
    normal2 (T.point 0-T.point 1)] : Fin 3 → E 2) i
noncomputable def support (i : Fin 3) : ℝ :=
  ⟪T.raw i,(![T.point 1,T.point 2,T.point 0] : Fin 3 → E 2) i⟫

lemma width_pos : 0 < T.determinant^2 := sq_pos_of_ne_zero T.det_ne

lemma raw_eval (i j : Fin 3) :
    ⟪T.raw i,T.point j⟫=T.support i-(if i=j then T.determinant^2 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [raw,support,determinant,normal2,det2,LemmaB.Eight.inner_E2] <;> ring

lemma raw_sum : ∑ i,T.raw i=0 := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three,raw,normal2] <;> ring

lemma support_sum : ∑ i,T.support i=T.determinant^2 := by
  have h := congrArg (fun n : E 2 => ⟪n,T.point 0⟫) T.raw_sum
  rw [sum_inner,inner_zero_left] at h
  simp only [T.raw_eval] at h
  simp [Fin.sum_univ_three] at h ⊢
  linarith

lemma raw_ne_zero (i : Fin 3) : T.raw i ≠ 0 := by
  intro h
  have hj : ∃ j : Fin 3,i ≠ j := by fin_cases i <;> decide
  obtain ⟨j,hj⟩ := hj
  have h0 := T.raw_eval i i
  have h1 := T.raw_eval i j
  rw [h,inner_zero_left,if_pos rfl] at h0
  rw [h,inner_zero_left,if_neg hj] at h1
  linarith [T.width_pos]

noncomputable def normal (i : Fin 3) : E 2 := ‖T.raw i‖⁻¹ • T.raw i
noncomputable def height (i : Fin 3) : ℝ := ‖T.raw i‖⁻¹*T.support i
noncomputable def width (i : Fin 3) : ℝ := ‖T.raw i‖⁻¹*T.determinant^2

lemma normal_unit (i : Fin 3) : ‖T.normal i‖=1 := by
  rw [normal,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 (norm_pos_iff.2 (T.raw_ne_zero i))),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (T.raw_ne_zero i))]

lemma width_positive (i : Fin 3) : 0 < T.width i :=
  mul_pos (inv_pos.2 (norm_pos_iff.2 (T.raw_ne_zero i))) T.width_pos

lemma normal_eval (i j : Fin 3) :
    ⟪T.normal i,T.point j⟫=T.height i-(if i=j then T.width i else 0) := by
  rw [normal,real_inner_smul_left,T.raw_eval]
  by_cases h : i=j <;> simp [h,height,width,mul_sub]

lemma point_injective : Function.Injective T.point := by
  intro i j h
  by_contra hij
  have h0 := T.normal_eval i i
  have h1 := T.normal_eval i j
  rw [h] at h0
  rw [if_pos rfl] at h0
  rw [if_neg hij] at h1
  linarith [T.width_positive i]

lemma normal_injective : Function.Injective T.normal := by
  intro i j h
  by_contra hij
  have h0 := T.normal_eval i i
  have h1 := T.normal_eval i j
  have h2 := T.normal_eval j i
  have h3 := T.normal_eval j j
  rw [h] at h0 h1
  simp [hij,Ne.symm hij] at h0 h1 h2 h3
  linarith [T.width_positive i,T.width_positive j]

lemma no_opposite (i j : Fin 3) : T.normal i ≠ -T.normal j := by
  intro h
  obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3,k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  have h0 := T.normal_eval i i
  have h1 := T.normal_eval i k
  have h2 := T.normal_eval j i
  have h3 := T.normal_eval j k
  rw [h,inner_neg_left] at h0 h1
  simp [Ne.symm hki,Ne.symm hkj] at h0 h1 h3
  by_cases hij : j=i
  · simp only [if_pos hij] at h2
    linarith [T.width_positive i,T.width_positive j]
  · simp only [if_neg hij] at h2
    linarith [T.width_positive i]

/-- Every translate of a triangle has a strictly positive supporting edge. -/
theorem exists_positive_support (q : E 2) : ∃ i,T.height i+⟪T.normal i,q⟫ > 0 := by
  have hsum : ∑ i,(T.support i+⟪T.raw i,q⟫)=T.determinant^2 := by
    rw [Finset.sum_add_distrib,← sum_inner,T.raw_sum,inner_zero_left,add_zero,T.support_sum]
  have hex : ∃ i,T.support i+⟪T.raw i,q⟫ > 0 := by
    by_contra h
    push Not at h
    have hle := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    rw [hsum] at hle
    linarith [T.width_pos]
  obtain ⟨i,hi⟩ := hex
  refine ⟨i,?_⟩
  rw [height,normal,real_inner_smul_left,← mul_add]
  exact mul_pos (inv_pos.2 (norm_pos_iff.2 (T.raw_ne_zero i))) hi

end TriangleData
end Kalai5.Cube3
