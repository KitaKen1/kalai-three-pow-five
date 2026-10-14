import Kalai5.Cube3.TriangleNormals

/-! Extract a genuine signed triangle from a three-point class. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma triangle_det_ne {p : Fin 3 → E 2} (hp : Function.Injective p)
    (h2 : dim (range p)=2) : det2 (p 1-p 0) (p 2-p 0) ≠ 0 := by
  intro hd
  have h10 : p 1-p 0 ≠ 0 := sub_ne_zero.2 (fun h => (by decide : (1 : Fin 3) ≠ 0) (hp h))
  have hc : ∀ y ∈ range p,⟪y,normal2 (p 1-p 0)⟫=⟪p 0,normal2 (p 1-p 0)⟫ := by
    rintro y ⟨i,rfl⟩
    rw [real_inner_comm (normal2 (p 1-p 0)) (p i),real_inner_comm (normal2 (p 1-p 0)) (p 0)]
    apply sub_eq_zero.1
    rw [← inner_sub_right,normal2_inner]
    fin_cases i
    · simp [det2]
    · simp [det2]; ring
    · exact hd
  have hle := LemmaB.dim_le_one_of_const (normal2_ne_zero h10) hc
  omega

variable {x : Fin 8 → E5} (C : Config x)

structure TriangleFibre (j : Fin 4) where
  vertex : Fin 3 → Fin 8
  inj : Function.Injective vertex
  cls : ∀ i,C.c (vertex i)=j
  covers : ∀ v,C.c v=j → ∃ i,vertex i=v
  triangle : TriangleData
  point_eq : ∀ i,triangle.point i=C.signedPoint (vertex i)

namespace Config

lemma signedPoint_inj {v w : Fin 8} (hc : C.c v=C.c w)
    (h : C.signedPoint v=C.signedPoint w) : v=w := by
  apply C.inj v w hc
  have he := congrArg (fun q : E 2 => balanceSign (C.c v) • q) h
  simpa only [signedPoint,← hc,smul_smul,balanceSign_sq,one_smul] using he

theorem triangle_fibre {j : Fin 4} (h3 : (C.cls j).card=3) : Nonempty (TriangleFibre C j) := by
  classical
  let e : C.cls j ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using h3)
  let v : Fin 3 → Fin 8 := fun i => (e.symm i).val
  have hv : ∀ i,C.c (v i)=j := by
    intro i; exact (Finset.mem_filter.1 (e.symm i).property).2
  have hv_inj : Function.Injective v := by
    intro i k h; exact e.symm.injective (Subtype.ext h)
  have hv_cov : ∀ w,C.c w=j → ∃ i,v i=w := by
    intro w hw
    refine ⟨e ⟨w,by simp [cls,hw]⟩,?_⟩
    simp [v]
  let p : Fin 3 → E 2 := fun i => C.k (v i)
  have hp : Function.Injective p := by
    intro i k h; exact hv_inj (C.inj _ _ ((hv i).trans (hv k).symm) h)
  have hrange : range p=(fibre C.c C.k j : Set (E 2)) := by
    ext q
    constructor
    · rintro ⟨i,rfl⟩; exact Finset.mem_image.2 ⟨v i,by simp [hv],rfl⟩
    · intro h
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.1 h
      obtain ⟨i,rfl⟩ := hv_cov w (by simpa using hw)
      exact ⟨i,rfl⟩
  have hdim : dim (range p)=2 := by
    have hh := C.dim_fibre_eq_two (j := j) (by omega)
    rw [← hrange] at hh
    unfold dim at hh ⊢
    rwa [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan] at hh
  have hd := triangle_det_ne hp hdim
  have hdet : det2 (C.signedPoint (v 1)-C.signedPoint (v 0))
      (C.signedPoint (v 2)-C.signedPoint (v 0))=det2 (p 1-p 0) (p 2-p 0) := by
    simp only [signedPoint,hv]
    calc
      _ = (balanceSign j*balanceSign j)*det2 (p 1-p 0) (p 2-p 0) := by
        simp [det2,p]; ring
      _ = _ := by rw [balanceSign_sq,one_mul]
  refine ⟨⟨v,hv_inj,hv,hv_cov,⟨fun i => C.signedPoint (v i),?_⟩,fun _ => rfl⟩⟩
  rwa [hdet]

end Config

namespace TriangleFibre
variable {C} {j : Fin 4} (T : TriangleFibre C j)

lemma evaluation (i k : Fin 3) :
    ⟪T.triangle.normal i,C.signedPoint (T.vertex k)⟫=
      T.triangle.height i-(if i=k then T.triangle.width i else 0) := by
  rw [← T.point_eq]; exact T.triangle.normal_eval i k

lemma upper (i : Fin 3) (v : Fin 8) (hv : C.c v=j) :
    ⟪T.triangle.normal i,C.signedPoint v⟫≤T.triangle.height i := by
  obtain ⟨k,rfl⟩ := T.covers v hv
  rw [T.evaluation]
  split_ifs <;> linarith [T.triangle.width_positive i]

lemma edge_points (i : Fin 3) : ∃ a b : Fin 3,a ≠ b ∧ i ≠ a ∧ i ≠ b := by
  fin_cases i <;> decide

end TriangleFibre
end Kalai5.Cube3
