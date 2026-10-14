import Kalai5.Cube3.TranslatedTriangleFrame

/-! Realize a balanced three-coordinate corner in both translated triangle classes. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}
namespace TranslatedTriangleFrame
variable (F : TranslatedTriangleFrame C)

theorem realize_same_values (f : Fin 3 → ℝ) (hf : ∀ i,|f i|≤1) (hbal : ∑ i,F.beta i*f i=0) :
    ∃ p : E5,p ∈ C.polarModel ∧ C.signedValue p F.v=1 ∧ C.signedValue p F.w= -1 ∧
      (∀ i,C.signedValue p (F.T.vertex i)=f i) ∧
      (∀ i,C.signedValue p (F.U.vertex (F.pairing i))=f i) := by
  obtain ⟨a,b,he,heval⟩ := F.T.triangle.affine_interpolation f
  have ha : a+⟪b,F.anchor⟫=0 := by
    rw [heval]
    simpa only [beta,mul_comm] using hbal
  let u : Fin 4 → ℝ := fun j =>
    (![1-⟪b,C.signedPoint F.v⟫,-1-⟪b,C.signedPoint F.w⟫,a,a-⟪b,F.shift⟫] : Fin 4 → ℝ) (F.order.symm j)
  have hu (j : Fin 4) : u (F.order j)=
      (![1-⟪b,C.signedPoint F.v⟫,-1-⟪b,C.signedPoint F.w⟫,a,a-⟪b,F.shift⟫] : Fin 4 → ℝ) j := by simp [u]
  have huz : ∑ j,u j=0 := by
    dsimp [u]
    rw [Equiv.sum_comp F.order.symm,Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    change (1-⟪b,C.signedPoint F.v⟫)+(-1-⟪b,C.signedPoint F.w⟫)+a+(a-⟪b,F.shift⟫)=0
    rw [anchor,inner_smul_right,inner_add_right,inner_add_right] at ha
    linarith
  let p := pack (signedOffsets u) b
  have hv : C.signedValue p F.v=1 := by
    rw [C.signedValue_pack huz,F.cv,hu]; simp
  have hw : C.signedValue p F.w= -1 := by
    rw [C.signedValue_pack huz,F.cw,hu]; simp
  have hT (i : Fin 3) : C.signedValue p (F.T.vertex i)=f i := by
    rw [C.signedValue_pack huz,F.T.cls,hu]
    change a+⟪b,C.signedPoint (F.T.vertex i)⟫=f i
    rw [← F.T.point_eq]; exact he i
  have hU (i : Fin 3) : C.signedValue p (F.U.vertex (F.pairing i))=f i := by
    rw [C.signedValue_pack huz,F.U.cls,hu]
    change a-⟪b,F.shift⟫+⟪b,C.signedPoint (F.U.vertex (F.pairing i))⟫=f i
    rw [← F.U.point_eq,F.translated,inner_add_right]
    linarith [he i]
  refine ⟨p,?_,hv,hw,hT,hU⟩
  apply (C.mem_polar_signed p).2
  intro z
  obtain ⟨j,hj⟩ := F.order.surjective (C.c z)
  have hz : C.c z=F.order j := hj.symm
  fin_cases j
  · rw [C.eq_of_singleton_class F.single0 hz F.cv,hv]; norm_num
  · rw [C.eq_of_singleton_class F.single1 hz F.cw,hw]; norm_num
  · obtain ⟨i,rfl⟩ := F.T.covers z hz
    rw [hT]; exact hf i
  · obtain ⟨i,rfl⟩ := F.U.covers z hz
    obtain ⟨j,rfl⟩ := F.pairing.surjective i
    rw [hU]; exact hf j

lemma matching_difference (p : E5) (i j : Fin 3) :
    C.signedValue p (F.U.vertex (F.pairing i))-C.signedValue p (F.T.vertex i)=
      C.signedValue p (F.U.vertex (F.pairing j))-C.signedValue p (F.T.vertex j) := by
  simp only [C.signedValue_eq,F.T.cls,F.U.cls,← F.T.point_eq,← F.U.point_eq,
    F.translated,inner_add_right]
  ring

lemma matching_of_one (p : E5) {j : Fin 3}
    (he : C.signedValue p (F.U.vertex (F.pairing j))=C.signedValue p (F.T.vertex j)) :
    ∀ i,C.signedValue p (F.U.vertex (F.pairing i))=C.signedValue p (F.T.vertex i) := by
  intro i
  have hh := F.matching_difference p i j
  rw [he,sub_self] at hh
  exact sub_eq_zero.1 hh

end TranslatedTriangleFrame
end Kalai5.Cube3
