import Kalai5.Cube3.ZeroCoordinateCount
import Kalai5.Cube3.SegmentFibre
import Kalai5.Cube3.TwoWidthExceptional

/-! Saturation of a zero-width segment transfers the entire marked family to the actual polar. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}
namespace TwoWidthSlice
variable (F : TwoWidthSlice C) (S : SegmentFibre C (F.order 0))

lemma zero_segment_value (z : SlabPoint) (v : Fin 8) (hv : C.c v=F.order 0) :
    C.signedValue (F.embed z) v=z.1 0 := by
  have hrad : F.intervals.radius (F.order 0)=0 := F.zero 0
  have hh := F.intervals.projected_bound v
  rw [hv,hrad] at hh
  have he := abs_eq_zero.1 (le_antisymm hh (abs_nonneg _))
  rw [F.intervals.value_centered,F.centerEval_embed,hv,F.coords_order,F.planar_embed,
    real_inner_smul_left,he,mul_zero,add_zero]
  rfl

include S in
theorem zero_family {ι : Type*} (G : ZeroDoubleFamily F.ratio F.eta ι)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C ι,∀ i,H.normal i=n := by
  have hm (i : ι) : F.embed (G.point i) ∈ C.polarModel.extremePoints ℝ :=
    F.embed_extreme (G.extreme i) (G.positive i).ne'
      (S.first_class.trans S.second_class.symm)
      (fun h => S.distinct (C.signedPoint_inj (S.first_class.trans S.second_class.symm) h.symm))
      (G.zero_saturated i) (F.zero_segment_value _ _ S.first_class) (F.zero_segment_value _ _ S.second_class)
  have hr (i : ι) : ∃ t : ℝ,0 < t ∧ planar (F.embed (G.point i))=t • n := by
    refine ⟨(G.point i).2*a,mul_pos (G.positive i) ha,?_⟩
    rw [F.planar_embed,he,smul_smul]
  exact ⟨PositiveFamily.onRay n hn (fun i => F.embed (G.point i))
    (F.embed_injective.comp G.inj) hm hr,fun _ => rfl⟩

include S in
theorem zero_three (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Unit),∀ i,H.normal i=n := by
  obtain ⟨h0,_,_⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_zero_three F.ratio_pos F.ratio_le h0
  exact F.zero_family S G hn ha he

end TwoWidthSlice
end Kalai5.Cube3
