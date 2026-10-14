import Kalai5.Cube3.TripleSlabCount

/-! Three positive slab vertices saturating one prescribed zero-width segment coordinate. -/
namespace Kalai5.Cube3
open Set

theorem tripleSlab_segment_three_nonnegative {η : ℝ} (hη : 0 ≤ η) :
    ∃ G : SlabFamily η (Fin 3),∀ i,(G.point i).1 0=1 ∨ (G.point i).1 0= -1 := by
  by_cases h1 : 1 < η
  · refine ⟨upperThree h1,?_⟩
    intro i; fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hbound : |η|≤1 := by rw [abs_of_nonneg hη]; exact le_of_not_gt h1
  let F := SlabFamily.capCycle (a := 1) (b := -1) (c := η)
    (Or.inl rfl) (Or.inr rfl) hbound (by ring) (Or.inl (by norm_num))
  let G := SlabFamily.capCycle (a := -1) (b := 1) (c := η)
    (Or.inr rfl) (Or.inl rfl) hbound (by ring) (Or.inl (by norm_num))
  let f : Fin 3 → SlabPoint := ![F.point 0,G.point 2,G.point 0]
  have hf01 : f 0 ≠ f 1 := by
    intro he
    have hh := congrArg (fun z : SlabPoint => z.1 1) he
    change (-1 : ℝ)=η at hh; linarith
  have hf02 : f 0 ≠ f 2 := by
    intro he
    have hh := congrArg (fun z : SlabPoint => z.1 0) he
    change (1 : ℝ)= -1 at hh; norm_num at hh
  have hf12 : f 1 ≠ f 2 := by
    intro he
    have hh := congrArg (fun z : SlabPoint => z.1 0) he
    change (1 : ℝ)= -1 at hh; norm_num at hh
  have hinj : Function.Injective f := by
    intro i j he; fin_cases i <;> fin_cases j <;> simp_all
  have hs (i : Fin 3) : (f i).1 0=1 ∨ (f i).1 0= -1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨⟨f,hinj,?_,?_,fun i => ⟨0,hs i⟩⟩,hs⟩
  · intro i; fin_cases i
    · exact F.extreme 0
    · exact G.extreme 2
    · exact G.extreme 0
  · intro i; fin_cases i <;> norm_num [f,F,G,SlabFamily.capCycle]

theorem tripleSlab_segment_three (η : ℝ) :
    ∃ G : SlabFamily η (Fin 3),∀ i,(G.point i).1 0=1 ∨ (G.point i).1 0= -1 := by
  by_cases hη : 0 ≤ η
  · exact tripleSlab_segment_three_nonnegative hη
  obtain ⟨F,hF⟩ := tripleSlab_segment_three_nonnegative (by linarith : 0 ≤ -η)
  have hs (i : Fin 3) : (slabFlip (F.point i)).1 0=1 ∨ (slabFlip (F.point i)).1 0= -1 := by
    rcases hF i with h | h
    · exact Or.inr (by change -(F.point i).1 0= -1; rw [h])
    · exact Or.inl (by change -(F.point i).1 0=1; rw [h]; norm_num)
  refine ⟨⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,
    fun i => ⟨0,hs i⟩⟩,hs⟩
  intro i
  have he : slabFlip '' tripleSlab (-η)=tripleSlab η := by simpa using tripleSlab_flip (-η)
  rw [← he,← image_extremePoints]
  exact ⟨F.point i,F.extreme i,rfl⟩

end Kalai5.Cube3
