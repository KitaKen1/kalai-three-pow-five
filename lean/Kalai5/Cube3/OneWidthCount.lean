import Kalai5.Cube3.OneWidthExceptional
import Kalai5.Cube3.SlabSaturation
import Kalai5.Cube3.PositiveSigma

/-! Two zero-width segment fibres lift all five slab vertices, even when the singleton saturates. -/
namespace Kalai5.Cube3
open Set
variable {x : Fin 8 → E5} {C : Config x}
namespace OneWidthSlice
variable (F : OneWidthSlice C)

theorem two_segments_family (S : SegmentFibre C (F.order 0)) (R : SegmentFibre C (F.order 1))
    {ι : Type*} (G : SlabFamily F.eta ι)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C ι,∀ i,H.normal i=n := by
  have hm (i : ι) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ := by
    obtain ⟨j,hj⟩ := tripleSlab_first_two_saturated (G.extreme i)
    have hseg (j : Fin 3) (U : SegmentFibre C (F.order j.castSucc))
        (hs : (G.point i).1 j=1 ∨ (G.point i).1 j= -1) :
        F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ :=
      F.embed_extreme (G.extreme i) (G.positive i).ne'
        (U.first_class.trans U.second_class.symm)
        (fun h => U.distinct (C.signedPoint_inj (U.first_class.trans U.second_class.symm) h.symm))
        hs (F.zero_value _ j _ U.first_class) (F.zero_value _ j _ U.second_class)
    fin_cases j
    · exact hseg 0 S hj
    · exact hseg 1 R hj
  have hr (i : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed,he,smul_smul]
  exact ⟨PositiveFamily.onRay n hn (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hm hr,fun _ => rfl⟩

theorem five_positive (S : SegmentFibre C (F.order 0)) (R : SegmentFibre C (F.order 1))
    (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 3 ⊕ Fin 2),∀ i,H.normal i=n := by
  obtain ⟨h1,hm1,h3,hm3⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := tripleSlab_five h1 hm1 h3 hm3
  exact F.two_segments_family S R G hn ha he

end OneWidthSlice
end Kalai5.Cube3
