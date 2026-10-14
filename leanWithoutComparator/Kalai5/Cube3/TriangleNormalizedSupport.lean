import Kalai5.Cube3.TriangleNormals

/-! Width-normalized supporting values have total one, independently of translation. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem normalized_support_sum (T : TriangleData) (q : E 2) :
    (∑ i,(T.height i+⟪T.normal i,q⟫)/T.width i)=1 := by
  have he (i : Fin 3) : (T.height i+⟪T.normal i,q⟫)/T.width i=
      (T.support i+⟪T.raw i,q⟫)/T.determinant^2 := by
    have hn := norm_ne_zero_iff.2 (T.raw_ne_zero i)
    have hd := T.width_pos.ne'
    simp only [height,normal,width,real_inner_smul_left]
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div,Finset.sum_add_distrib,← sum_inner,T.raw_sum,inner_zero_left,
    add_zero,T.support_sum,div_self T.width_pos.ne']

theorem normalized_support_three (T : TriangleData) (q : E 2) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (T.height i+⟪T.normal i,q⟫)/T.width i+
      (T.height j+⟪T.normal j,q⟫)/T.width j+
      (T.height k+⟪T.normal k,q⟫)/T.width k=1 := by
  have hh := T.normalized_support_sum q
  rw [Fin.sum_univ_three] at hh
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> linarith

end Kalai5.Cube3.TriangleData
