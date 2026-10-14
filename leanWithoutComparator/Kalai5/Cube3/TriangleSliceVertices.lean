import Kalai5.Cube3.DoubleUpperCount

/-! A triangle supporting the wider interval turns all four marked slice vertices
into distinct vertices of the actual five-dimensional polar. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

lemma ProjectionIntervals.triangle_upper_eq {n : E 2} (I : ProjectionIntervals C n)
    {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3) {a : ℝ} (ha : 0 < a)
    (hn : n=a • T.triangle.normal i) (k : Fin 3) (hk : i ≠ k) :
    ⟪n,C.signedPoint (T.vertex k)⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  have hscale (v : Fin 8) : ⟪n,C.signedPoint v⟫=a*⟪T.triangle.normal i,C.signedPoint v⟫ := by
    exact (congrArg (fun b : E 2 => ⟪b,C.signedPoint v⟫) hn).trans (real_inner_smul_left _ _ _)
  have he : ⟪n,C.signedPoint (T.vertex k)⟫=a*T.triangle.height i := by
    rw [hscale,T.evaluation,if_neg hk,sub_zero]
  have hup : ⟪n,C.signedPoint (I.hi j)⟫≤a*T.triangle.height i := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (T.upper i _ (I.chi j)) ha.le
  have hlo := I.upper (T.vertex k)
  rw [T.cls,he] at hlo
  exact he.trans (le_antisymm hup hlo).symm

namespace TwoWidthSlice
variable (F : TwoWidthSlice C)

theorem triangle_upper_family {ι : Type*} (G : UpperDoubleFamily F.ratio F.eta ι)
    (T : TriangleFibre C (F.order 3)) (i : Fin 3) {a : ℝ} (ha : 0 < a)
    (hn : F.normal=a • T.triangle.normal i) :
    ∃ H : PositiveFamily C ι,∀ k,H.normal k=T.triangle.normal i := by
  obtain ⟨v,w,hvw,hiv,hiw⟩ := TriangleFibre.edge_points i
  have hneq : C.signedPoint (T.vertex w) ≠ C.signedPoint (T.vertex v) := by
    intro he
    exact hvw (T.inj (C.signedPoint_inj ((T.cls v).trans (T.cls w).symm) he.symm))
  have hm (k : ι) : F.embed (G.point k) ∈ C.polarModel.extremePoints ℝ := by
    apply F.upper_edge_extreme (G.extreme k) (G.positive k).ne' (T.cls v) (T.cls w) hneq
      (F.intervals.triangle_upper_eq T i ha hn v hiv)
      (F.intervals.triangle_upper_eq T i ha hn w hiw)
    rw [F.coords_order,F.unit,mul_one]
    change F.eta*(G.point k).2-(∑ j,(G.point k).1 j)+(G.point k).2=1
    have hh := G.upper k
    change 1*(F.eta*(G.point k).2-∑ j,(G.point k).1 j)+(G.point k).2=1 at hh
    simpa only [one_mul] using hh
  have hr (k : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point k))=t • T.triangle.normal i := by
    refine ⟨(G.point k).2*a,mul_pos (G.positive k) ha,?_⟩
    rw [F.planar_embed,hn,smul_smul]
  exact ⟨PositiveFamily.onRay _ (T.triangle.normal_unit i) (fun k => F.embed (G.point k))
    (F.embed_injective.comp G.inj) hm hr,fun _ => rfl⟩

theorem triangle_upper_four (T : TriangleFibre C (F.order 3)) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : F.normal=a • T.triangle.normal i)
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM) (hη : 0 ≤ F.eta) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Fin 2),∀ k,H.normal k=T.triangle.normal i := by
  obtain ⟨h0,h2,_⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_upper_four F.ratio_pos F.ratio_le hη h0 h2
  exact F.triangle_upper_family G T i ha hn

end TwoWidthSlice
end Kalai5.Cube3
