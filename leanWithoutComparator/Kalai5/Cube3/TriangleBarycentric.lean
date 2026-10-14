import Kalai5.Cube3.TriangleNormalizedSupport

/-! Affine coordinates dual to the three normalized supporting functions. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def barycentric (T : TriangleData) (p : E 2) (i : Fin 3) : ℝ :=
  (T.height i-⟪T.normal i,p⟫)/T.width i

lemma barycentric_raw (T : TriangleData) (p : E 2) (i : Fin 3) :
    T.barycentric p i=(T.support i-⟪T.raw i,p⟫)/T.determinant^2 := by
  have hn := norm_ne_zero_iff.2 (T.raw_ne_zero i)
  have hd := T.width_pos.ne'
  simp only [barycentric,height,normal,width,real_inner_smul_left]
  field_simp

theorem barycentric_sum (T : TriangleData) (p : E 2) : ∑ i,T.barycentric p i=1 := by
  simpa only [barycentric,inner_neg_right,sub_eq_add_neg] using T.normalized_support_sum (-p)

theorem barycentric_reconstruct (T : TriangleData) (p : E 2) :
    ∑ i,T.barycentric p i • T.point i=p := by
  have hd := T.width_pos.ne'
  ext k
  rw [Fin.sum_univ_three]
  change T.barycentric p 0*T.point 0 k+T.barycentric p 1*T.point 1 k+
    T.barycentric p 2*T.point 2 k=p k
  rw [T.barycentric_raw,T.barycentric_raw,T.barycentric_raw]
  field_simp [hd]
  apply (div_eq_iff hd).2
  fin_cases k <;> simp [raw,support,determinant,normal2,det2,LemmaB.Eight.inner_E2] <;> ring

theorem normals_separate (T : TriangleData) {p q : E 2}
    (h : ∀ i,⟪T.normal i,p⟫=⟪T.normal i,q⟫) : p=q := by
  have hb : T.barycentric p=T.barycentric q := by funext i; simp only [barycentric,h]
  rw [← T.barycentric_reconstruct p,hb,T.barycentric_reconstruct q]

end Kalai5.Cube3.TriangleData
