import Kalai5.Cube3.TriangleFibre

/-! Lift all three signed triangle normals, and obtain a fourth vertex from two singleton classes. -/

namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} {C : Config x}

namespace TriangleFibre
variable {j : Fin 4} (T : TriangleFibre C j)

lemma unsigned_normal (i : Fin 3) :
    LemmaB.IsEdgeNormal (fibre C.c C.k j) (balanceSign j • T.triangle.normal i) := by
  have he (v : Fin 8) (hv : C.c v=j) :
      ⟪balanceSign j • T.triangle.normal i,C.k v⟫=⟪T.triangle.normal i,C.signedPoint v⟫ := by
    simp [Config.signedPoint,hv,real_inner_smul_left,inner_smul_right]
  have hm (a : Fin 3) (ha : i ≠ a) : C.k (T.vertex a) ∈
      LemmaB.amax (fibre C.c C.k j) (balanceSign j • T.triangle.normal i) := by
    apply LemmaB.mem_amax.2
    refine ⟨Finset.mem_image.2 ⟨T.vertex a,by simp [T.cls],rfl⟩,?_⟩
    intro q hq
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hq
    have hv' : C.c v=j := by simpa using hv
    rw [he v hv',he _ (T.cls a),T.evaluation,if_neg ha,sub_zero]
    exact T.upper i v hv'
  refine ⟨?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,balanceSign_abs,T.triangle.normal_unit,one_mul]
  · obtain ⟨a,b,hab,hia,hib⟩ := edge_points i
    apply Finset.one_lt_card.2
    refine ⟨_,hm a hia,_,hm b hib,?_⟩
    intro h; exact hab (T.inj (C.inj _ _ ((T.cls a).trans (T.cls b).symm) h))

theorem ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (i : Fin 3) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,∃ t : ℝ,0 < t ∧ planar p=t • T.triangle.normal i := by
  obtain ⟨p,hp,t,ht,hpt⟩ := C.edge_ray_vertex hP hrange j (T.unsigned_normal i)
  rcases balanceSign_sign j with hs | hs
  · rw [hs,one_smul] at hpt
    exact ⟨p,hp,t,ht,hpt⟩
  · refine ⟨-p,C.polarModel_neg_extreme hp,t,ht,?_⟩
    rw [planar_neg,hpt,hs,neg_one_smul,smul_neg,neg_neg]

theorem one_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (i : Fin 3) :
    ∃ F : PositiveFamily C Unit,∀ k,F.normal k=T.triangle.normal i := by
  obtain ⟨p,hp,hr⟩ := T.ray_vertex hP hrange i
  exact ⟨PositiveFamily.onRay _ (T.triangle.normal_unit i) (fun _ : Unit => p)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hp) (fun _ => hr),fun _ => rfl⟩

end TriangleFibre

lemma Config.eq_of_singleton_class {j : Fin 4} (h1 : (C.cls j).card=1)
    {v w : Fin 8} (hv : C.c v=j) (hw : C.c w=j) : v=w := by
  exact Finset.card_le_one.1 h1.le v (by simp [Config.cls,hv]) w (by simp [Config.cls,hw])

namespace TriangleFibre

theorem bonus_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 0))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    ∃ i,∃ F : PositiveFamily C (Fin 2),∀ k,F.normal k=T.triangle.normal i := by
  let r : Fin 4 → Fin 8 := fun j => (C.surj (τ j)).choose
  have hr : ∀ j,C.c (r j)=τ j := fun j => (C.surj (τ j)).choose_spec
  let q := C.signedPoint (r 1)+C.signedPoint (r 2)+C.signedPoint (r 3)
  obtain ⟨i,hi⟩ := T.triangle.exists_positive_support q
  obtain ⟨a,b,hab,hia,hib⟩ := edge_points i
  let rep : Fin 4 → Fin 8 := ![T.vertex a,r 1,r 2,r 3]
  have hc : ∀ j,C.c (rep j)=τ j := by
    intro j; fin_cases j
    · exact T.cls a
    · exact hr 1
    · exact hr 2
    · exact hr 3
  have ha : ⟪T.triangle.normal i,C.signedPoint (rep 0)⟫=T.triangle.height i := by
    change ⟪T.triangle.normal i,C.signedPoint (T.vertex a)⟫=_
    rw [T.evaluation,if_neg hia,sub_zero]
  have hb : ⟪T.triangle.normal i,C.signedPoint (T.vertex b)⟫=T.triangle.height i := by
    rw [T.evaluation,if_neg hib,sub_zero]
  obtain ⟨f,hf,he,hf_ray⟩ := C.edge_two_vertices hP hrange τ rep hc (T.vertex b) (T.cls b)
    (fun h => hab (T.inj (C.signedPoint_inj ((T.cls a).trans (T.cls b).symm) h.symm)))
    (T.triangle.normal i) (T.triangle.normal_unit i) (hb.trans ha.symm)
    (fun v hv => by rw [ha]; exact T.upper i v hv)
    (fun v hv => congrArg (fun w => ⟪T.triangle.normal i,C.signedPoint w⟫)
      (C.eq_of_singleton_class h2 hv (hc 2)))
    (fun v hv => congrArg (fun w => ⟪T.triangle.normal i,C.signedPoint w⟫)
      (C.eq_of_singleton_class h3 hv (hc 3))) (by
      rw [Fin.sum_univ_four,inner_add_right,inner_add_right,inner_add_right,ha]
      simpa [rep,q,inner_add_right,add_assoc] using hi)
  exact ⟨i,PositiveFamily.onRay _ (T.triangle.normal_unit i) f hf he hf_ray,fun _ => rfl⟩

end TriangleFibre
end Kalai5.Cube3
