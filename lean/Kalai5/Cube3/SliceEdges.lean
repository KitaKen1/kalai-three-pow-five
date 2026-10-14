import Kalai5.Cube3.OpposedDoubleCount

/-! Actual saturated edges attached to either sign of either positive-width class. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

lemma ProjectionIntervals.triangle_lower_eq {n : E 2} (I : ProjectionIntervals C n)
    {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3) {a : ℝ} (ha : 0 < a)
    (hn : n=(-a) • T.triangle.normal i) (k : Fin 3) (hk : i ≠ k) :
    ⟪n,C.signedPoint (T.vertex k)⟫=⟪n,C.signedPoint (I.lo j)⟫ := by
  have hscale (v : Fin 8) : ⟪n,C.signedPoint v⟫=(-a)*⟪T.triangle.normal i,C.signedPoint v⟫ := by
    exact (congrArg (fun b : E 2 => ⟪b,C.signedPoint v⟫) hn).trans (real_inner_smul_left _ _ _)
  have he : ⟪n,C.signedPoint (T.vertex k)⟫=(-a)*T.triangle.height i := by
    rw [hscale,T.evaluation,if_neg hk,sub_zero]
  have hlo : (-a)*T.triangle.height i≤⟪n,C.signedPoint (I.lo j)⟫ := by
    rw [hscale]
    exact mul_le_mul_of_nonpos_left (T.upper i _ (I.clo j)) (by linarith)
  have hup := I.lower (T.vertex k)
  rw [T.cls,he] at hup
  exact he.trans (le_antisymm hup hlo).symm

structure SliceEdge (F : TwoWidthSlice C) (j : Fin 4) (σ : ℝ) where
  first : Fin 8
  second : Fin 8
  first_class : C.c first=j
  second_class : C.c second=j
  distinct : C.signedPoint second ≠ C.signedPoint first
  sign : σ=1 ∨ σ= -1
  active : ∀ z : SlabPoint,σ*F.coords z j+z.2*F.intervals.radius j=1 →
    C.signedValue (F.embed z) first=σ ∧ C.signedValue (F.embed z) second=σ

namespace TwoWidthSlice
variable (F : TwoWidthSlice C)

theorem triangle_upper_edge {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : F.normal=a • T.triangle.normal i) : Nonempty (SliceEdge F j 1) := by
  obtain ⟨v,w,hvw,hiv,hiw⟩ := TriangleFibre.edge_points i
  refine ⟨⟨T.vertex v,T.vertex w,T.cls v,T.cls w,?_,Or.inl rfl,?_⟩⟩
  · intro he; exact hvw (T.inj (C.signedPoint_inj ((T.cls v).trans (T.cls w).symm) he.symm))
  · intro z hz
    have hv := F.signed_eq_hi z (T.cls v) (F.intervals.triangle_upper_eq T i ha hn v hiv)
    have hw := F.signed_eq_hi z (T.cls w) (F.intervals.triangle_upper_eq T i ha hn w hiw)
    rw [one_mul] at hz
    exact ⟨hv.trans hz,hw.trans hz⟩

theorem triangle_lower_edge {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : F.normal=(-a) • T.triangle.normal i) : Nonempty (SliceEdge F j (-1)) := by
  obtain ⟨v,w,hvw,hiv,hiw⟩ := TriangleFibre.edge_points i
  refine ⟨⟨T.vertex v,T.vertex w,T.cls v,T.cls w,?_,Or.inr rfl,?_⟩⟩
  · intro he; exact hvw (T.inj (C.signedPoint_inj ((T.cls v).trans (T.cls w).symm) he.symm))
  · intro z hz
    have hv := F.signed_eq_lo z (T.cls v) (F.intervals.triangle_lower_eq T i ha hn v hiv)
    have hw := F.signed_eq_lo z (T.cls w) (F.intervals.triangle_lower_eq T i ha hn w hiw)
    constructor <;> linarith

theorem marked_family {ι : Type*} {σ τ : ℝ} (G : MarkedDoubleFamily F.ratio F.eta σ τ ι)
    (A : SliceEdge F (F.order 2) σ) (B : SliceEdge F (F.order 3) τ)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C ι,∀ k,H.normal k=n := by
  have hm (k : ι) : F.embed (G.point k) ∈ C.polarModel.extremePoints ℝ := by
    rcases G.marked k with hk | hk
    · have ha' : σ*F.coords (G.point k) (F.order 2)+
          (G.point k).2*F.intervals.radius (F.order 2)=1 := by
        rw [F.coords_order]
        change σ*(G.point k).1 2+(G.point k).2*F.ratio=1
        change σ*(G.point k).1 2+F.ratio*(G.point k).2=1 at hk
        nlinarith [hk]
      obtain ⟨hv,hw⟩ := A.active _ ha'
      exact F.embed_extreme (G.extreme k) (G.positive k).ne'
        (A.first_class.trans A.second_class.symm) A.distinct A.sign hv hw
    · have hb' : τ*F.coords (G.point k) (F.order 3)+
          (G.point k).2*F.intervals.radius (F.order 3)=1 := by
        rw [F.coords_order,F.unit,mul_one]
        exact hk
      obtain ⟨hv,hw⟩ := B.active _ hb'
      exact F.embed_extreme (G.extreme k) (G.positive k).ne'
        (B.first_class.trans B.second_class.symm) B.distinct B.sign hv hw
  have hr (k : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point k))=t • n := by
    refine ⟨(G.point k).2*a,mul_pos (G.positive k) ha,?_⟩
    rw [F.planar_embed,he,smul_smul]
  exact ⟨PositiveFamily.onRay n hn (fun k => F.embed (G.point k))
    (F.embed_injective.comp G.inj) hm hr,fun _ => rfl⟩

theorem opposed_three (A : SliceEdge F (F.order 2) 1) (B : SliceEdge F (F.order 3) (-1))
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Unit),∀ k,H.normal k=n := by
  obtain ⟨h0,_,hm2⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_opposed_three F.ratio_pos F.ratio_le h0 hm2
  exact F.marked_family G A B hn ha he

theorem opposed_three_reverse (A : SliceEdge F (F.order 2) (-1)) (B : SliceEdge F (F.order 3) 1)
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Unit),∀ k,H.normal k=n := by
  obtain ⟨h0,h2,_⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_opposed_three_reverse F.ratio_pos F.ratio_le h0 h2
  exact F.marked_family G A B hn ha he

end TwoWidthSlice
end Kalai5.Cube3
