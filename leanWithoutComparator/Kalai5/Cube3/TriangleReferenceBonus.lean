import Kalai5.Cube3.TriangleSupportIntervals

/-! Choose the representative of the other triangle before applying the edge bonus. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.two_positive_of_reference {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (i : Fin 3)
    (v w u : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1) (hu : C.c u=τ 3)
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1)
    (hpos : 0 < T.triangle.height i+⟪T.triangle.normal i,C.signedPoint u+C.signedPoint v+C.signedPoint w⟫) :
    ∃ F : PositiveFamily C (Fin 2),∀ k,F.normal k=T.triangle.normal i := by
  classical
  obtain ⟨a,b,hab,hia,hib⟩ := TriangleFibre.edge_points i
  let σ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hσ0 : σ 0=τ 2 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ1 : σ 1=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ2 : σ 2=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ3 : σ 3=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  let rep : Fin 4 → Fin 8 := ![T.vertex a,u,v,w]
  have hc : ∀ j,C.c (rep j)=σ j := by
    intro j; fin_cases j
    · exact (T.cls a).trans hσ0.symm
    · exact hu.trans hσ1.symm
    · exact hv.trans hσ2.symm
    · exact hw.trans hσ3.symm
  have ha : ⟪T.triangle.normal i,C.signedPoint (rep 0)⟫=T.triangle.height i := by
    change ⟪T.triangle.normal i,C.signedPoint (T.vertex a)⟫=_
    rw [T.evaluation,if_neg hia,sub_zero]
  have hb : ⟪T.triangle.normal i,C.signedPoint (T.vertex b)⟫=T.triangle.height i := by
    rw [T.evaluation,if_neg hib,sub_zero]
  obtain ⟨f,hf,he,hr⟩ := C.edge_two_vertices hP hrange σ rep hc (T.vertex b)
    ((T.cls b).trans hσ0.symm)
    (fun h => hab (T.inj (C.signedPoint_inj ((T.cls a).trans (T.cls b).symm) h.symm)))
    (T.triangle.normal i) (T.triangle.normal_unit i) (hb.trans ha.symm)
    (fun z hz => by rw [ha]; exact T.upper i z (hz.trans hσ0))
    (fun z hz => congrArg (fun z => ⟪T.triangle.normal i,C.signedPoint z⟫)
      (C.eq_of_singleton_class h0 (hz.trans hσ2) hv))
    (fun z hz => congrArg (fun z => ⟪T.triangle.normal i,C.signedPoint z⟫)
      (C.eq_of_singleton_class h1 (hz.trans hσ3) hw)) (by
      rw [Fin.sum_univ_four,inner_add_right,inner_add_right,inner_add_right,ha]
      simpa [rep,inner_add_right,add_assoc] using hpos)
  exact ⟨PositiveFamily.onRay _ (T.triangle.normal_unit i) f hf he hr,fun _ => rfl⟩

end Kalai5.Cube3
