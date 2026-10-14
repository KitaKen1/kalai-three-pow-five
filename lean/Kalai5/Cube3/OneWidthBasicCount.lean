import Kalai5.Cube3.NoSharedTriangleEdge

/-! A uniform three-vertex bound, including the exceptional offsets and three-level projections. -/
namespace Kalai5.Cube3
open Set
variable {x : Fin 8 → E5} {C : Config x}

theorem tripleSlab_three (η : ℝ) : Nonempty (SlabFamily η (Fin 3)) := by
  by_cases hsmall : |η| ≤ 1
  · exact ⟨SlabFamily.capCycle (a := 1) (b := -1) (c := η)
      (Or.inl rfl) (Or.inr rfl) hsmall (by ring) (Or.inl (by norm_num))⟩
  by_cases hpos : 1 < η
  · exact ⟨upperThree hpos⟩
  have hneg : 1 < -η := by
    have h := lt_of_not_ge hsmall
    rcases lt_abs.1 h with h | h
    · exact (hpos h).elim
    · linarith
  let F := upperThree hneg
  refine ⟨⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,?_⟩⟩
  · intro i
    have he : slabFlip '' tripleSlab (-η)=tripleSlab η := by simpa using tripleSlab_flip (-η)
    rw [← he,← image_extremePoints]
    exact ⟨F.point i,F.extreme i,rfl⟩
  · intro i
    obtain ⟨j,hj | hj⟩ := F.saturated i
    · exact ⟨j,Or.inr (by change -(F.point i).1 j= -1; rw [hj])⟩
    · exact ⟨j,Or.inl (by change -(F.point i).1 j=1; rw [hj]; norm_num)⟩

theorem OneWidthSlice.three_positive (F : OneWidthSlice C)
    (S : SegmentFibre C (F.order 0)) (R : SegmentFibre C (F.order 1))
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 3),∀ i,H.normal i=n := by
  obtain ⟨G⟩ := tripleSlab_three F.eta
  exact F.two_segments_family S R G hn ha he

theorem Config.parallel_segments_three (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 0)) (R : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (T : TriangleFibre C (τ 3))
    (hd : det2 S.direction R.direction=0) :
    ∃ H : PositiveFamily C (Fin 3),∀ i,H.normal i=S.normal := by
  have hn : S.normal ≠ 0 := by
    intro he; have hh := S.normal_unit; rw [he,norm_zero] at hh; norm_num at hh
  obtain ⟨F,horder,a,ha,he⟩ := Config.triangle_one_width_slice τ S R h2 T S.normal hn
    S.normal_orthogonal (S.unit_orthogonal_of_parallel R hd S.normal_unit S.normal_orthogonal)
  let S' := S.reclass (congrFun (congrArg Equiv.toFun horder) 0).symm
  let R' := R.reclass (congrFun (congrArg Equiv.toFun horder) 1).symm
  exact F.three_positive S' R' S.normal_unit ha he

end Kalai5.Cube3
