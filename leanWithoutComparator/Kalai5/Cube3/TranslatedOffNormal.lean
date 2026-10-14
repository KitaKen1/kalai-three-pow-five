import Kalai5.Cube3.TranslatedCorner

/-! A compact active face supplies an extreme point outside all triangle normal lines. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

lemma TriangleFibre.equal_values_on_ray {j : Fin 4} (T : TriangleFibre C j)
    (p : E5) (i k l : Fin 3) (hik : i ≠ k) (hil : i ≠ l) {t : ℝ}
    (hp : planar p=t • T.triangle.normal i) :
    C.signedValue p (T.vertex k)=C.signedValue p (T.vertex l) := by
  simp only [C.signedValue_eq,T.cls,hp,real_inner_smul_left,T.evaluation,
    if_neg hik,if_neg hil,sub_zero]

namespace TranslatedTriangleFrame
variable (F : TranslatedTriangleFrame C)

lemma planar_ne_zero_of_opposite_values (p : E5)
    (h0 : C.signedValue p (F.T.vertex 0)=1) (h1 : C.signedValue p (F.T.vertex 1)= -1) :
    planar p ≠ 0 := by
  intro he
  rw [C.signedValue_eq,F.T.cls,he,inner_zero_left,add_zero] at h0 h1
  linarith

lemma extra_of_corner_ray (p : E5)
    (hv : C.signedValue p F.v=1) (hw : C.signedValue p F.w= -1)
    (h0 : C.signedValue p (F.T.vertex 0)=1) (h1 : C.signedValue p (F.T.vertex 1)= -1)
    (hmatch : C.signedValue p (F.U.vertex (F.pairing 0))=1)
    (i : Fin 3) (t : ℝ) (hp : planar p=t • F.T.triangle.normal i) : C.ExtraPM := by
  have hsame := F.matching_of_one p (hmatch.trans h0.symm)
  have hT (k : Fin 3) : C.signedValue p (F.T.vertex k)=1 ∨ C.signedValue p (F.T.vertex k)= -1 := by
    fin_cases k
    · exact Or.inl h0
    · exact Or.inr h1
    · fin_cases i
      · exact Or.inr ((F.T.equal_values_on_ray p 0 2 1 (by decide) (by decide) hp).trans h1)
      · exact Or.inl ((F.T.equal_values_on_ray p 1 2 0 (by decide) (by decide) hp).trans h0)
      · have he := F.T.equal_values_on_ray p 2 0 1 (by decide) (by decide) hp
        rw [h0,h1] at he; norm_num at he
  have hsigned (z : Fin 8) : C.signedValue p z=1 ∨ C.signedValue p z= -1 := by
    obtain ⟨j,hj⟩ := F.order.surjective (C.c z)
    have hz : C.c z=F.order j := hj.symm
    fin_cases j
    · rw [C.eq_of_singleton_class F.single0 hz F.cv]; exact Or.inl hv
    · rw [C.eq_of_singleton_class F.single1 hz F.cw]; exact Or.inr hw
    · obtain ⟨k,rfl⟩ := F.T.covers z hz; exact hT k
    · obtain ⟨k,rfl⟩ := F.U.covers z hz
      obtain ⟨j,rfl⟩ := F.pairing.surjective k
      rw [hsame]; exact hT j
  refine ⟨offsets p,planar p,offsets_balanced p,F.planar_ne_zero_of_opposite_values p h0 h1,?_⟩
  intro z
  change C.value p z=1 ∨ C.value p z= -1
  have habs : |C.value p z|=1 := by
    rw [← C.signedValue_abs]
    rcases hsigned z with h | h <;> rw [h] <;> norm_num
  rcases le_total 0 (C.value p z) with h | h
  · exact Or.inl (by rwa [abs_of_nonneg h] at habs)
  · exact Or.inr (by rw [abs_of_nonpos h] at habs; linarith)

theorem off_normal_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,planar p ≠ 0 ∧
      ∀ i : Fin 3,∀ t : ℝ,planar p ≠ t • F.T.triangle.normal i := by
  classical
  obtain ⟨f,hf0,hf1,hf2,hbal⟩ := F.balanced_corner hP hrange hh hno
  have hf : ∀ i,|f i|≤1 := by
    intro i; fin_cases i
    · change |f 0|≤1; rw [hf0]; norm_num
    · change |f 1|≤1; rw [hf1]; norm_num
    · exact hf2.le
  obtain ⟨q,hq,hv,hw,hT,hU⟩ := F.realize_same_values f hf hbal
  have ht0 := (hT 0).trans hf0
  have ht1 := (hT 1).trans hf1
  have hu0 := (hU 0).trans hf0
  have hu1 := (hU 1).trans hf1
  let A : Finset (Fin 8) := {F.v,F.w,F.T.vertex 0,F.T.vertex 1,F.U.vertex (F.pairing 0),F.U.vertex (F.pairing 1)}
  have hs : ∀ z ∈ A,C.signedValue q z=1 ∨ C.signedValue q z= -1 := by
    intro z hz
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hw
    · exact Or.inl ht0
    · exact Or.inr ht1
    · exact Or.inl hu0
    · exact Or.inr hu1
  obtain ⟨p,hp,he,hpos⟩ := C.signed_activeFace_ray_vertex hP hrange A (C.signedValue q) hs (planar q)
    hq (fun _ _ => rfl) (real_inner_self_pos.2 (F.planar_ne_zero_of_opposite_values q ht0 ht1))
  have hv' := (he F.v (by simp [A])).trans hv
  have hw' := (he F.w (by simp [A])).trans hw
  have ht0' := (he (F.T.vertex 0) (by simp [A])).trans ht0
  have ht1' := (he (F.T.vertex 1) (by simp [A])).trans ht1
  have hu0' := (he (F.U.vertex (F.pairing 0)) (by simp [A])).trans hu0
  exact ⟨p,hp,F.planar_ne_zero_of_opposite_values p ht0' ht1',
    fun i t he => hno (F.extra_of_corner_ray p hv' hw' ht0' ht1' hu0' i t he)⟩

end TranslatedTriangleFrame
end Kalai5.Cube3
