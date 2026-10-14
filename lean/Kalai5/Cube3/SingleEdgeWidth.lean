import Kalai5.Cube3.OneWidthOpposed
import Kalai5.Cube3.SlabFour

/-! A zero-width segment and one polygon edge suffice to lift every positive slab vertex. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}
namespace ProjectionIntervals
variable {n m : E 2} (I : ProjectionIntervals C n)

lemma upper_pair_of_signed_edge {j : Fin 4}
    (hn : IsEdgeNormal (fibre C.c C.k j) (balanceSign j • m))
    {a : ℝ} (ha : 0 < a) (he : n=a • m) :
    ∃ v w : Fin 8,C.c v=j ∧ C.c w=j ∧ C.signedPoint w ≠ C.signedPoint v ∧
      ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ ∧
      ⟪n,C.signedPoint w⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  obtain ⟨v,w,hv,hw,hne,hvw,hmax⟩ := C.signed_support_pair hn
  have hscale (p : E 2) : ⟪n,p⟫=a*⟪m,p⟫ := by rw [he,real_inner_smul_left]
  have hbound := mul_le_mul_of_nonneg_left (hmax (I.hi j) (I.chi j)) ha.le
  have hvhi := I.upper v
  rw [hv,hscale,hscale] at hvhi
  have hvp : ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
    rw [hscale,hscale]; linarith
  refine ⟨v,w,hv,hw,hne,hvp,?_⟩
  rw [← hvp,hscale,hscale,hvw]

end ProjectionIntervals

namespace OneWidthSlice
variable (F : OneWidthSlice C)

theorem segment_edge_family (S : SegmentFibre C (F.order 0)) {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k (F.order 3)) (balanceSign (F.order 3) • n))
    {a : ℝ} (ha : 0 < a) (he : F.normal=a • n)
    {ι : Type*} (G : SlabFamily F.eta ι) :
    ∃ H : PositiveFamily C ι,∀ i,H.normal i=n := by
  have hnunit : ‖n‖=1 := by
    have hh := hn.1
    rwa [norm_smul,Real.norm_eq_abs,balanceSign_abs,one_mul] at hh
  obtain ⟨v,w,hv,hw,hvw,hvp,hwp⟩ := F.intervals.upper_pair_of_signed_edge hn ha he
  have hmemb (i : ι) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ := by
    rcases tripleSlab_segment_or_cap (G.extreme i) (G.positive i) with hs | hcap
    · exact F.embed_extreme (G.extreme i) (G.positive i).ne'
        (S.first_class.trans S.second_class.symm)
        (fun h => S.distinct (C.signedPoint_inj (S.first_class.trans S.second_class.symm) h.symm))
        hs (F.zero_value _ 0 _ S.first_class) (F.zero_value _ 0 _ S.second_class)
    · have hs := tripleSlab_positive_width_saturated (G.extreme i) (G.positive i).le
      rw [hcap] at hs
      have hzero : F.eta*1-∑ j,(G.point i).1 j=0 := by
        apply abs_eq_zero.1; linarith
      apply F.upper_edge_extreme (G.extreme i) (G.positive i).ne' hv hw hvw hvp hwp
      rw [F.coords_order,F.unit]
      change F.eta*(G.point i).2-∑ j,(G.point i).1 j+(G.point i).2*1=1
      rw [hcap,hzero]; norm_num
  have hr (i : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed]
    exact (congrArg (fun m : E 2 => (G.point i).2 • m) he).trans (smul_smul _ _ _)
  exact ⟨PositiveFamily.onRay n hnunit (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hmemb hr,fun _ => rfl⟩

theorem segment_edge_four (S : SegmentFibre C (F.order 0)) {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k (F.order 3)) (balanceSign (F.order 3) • n))
    {a : ℝ} (ha : 0 < a) (he : F.normal=a • n)
    (h1 : F.eta ≠ 1) (hm1 : F.eta ≠ -1) :
    ∃ H : PositiveFamily C (Fin 3 ⊕ Unit),∀ i,H.normal i=n := by
  obtain ⟨G⟩ := tripleSlab_four h1 hm1
  exact F.segment_edge_family S hn ha he G

end OneWidthSlice

end Kalai5.Cube3
