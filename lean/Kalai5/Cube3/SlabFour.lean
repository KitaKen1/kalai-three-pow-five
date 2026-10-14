import Kalai5.Cube3.SlabSegmentCap

/-! Four positive slab vertices away from the two genuine three-vertex boundaries. -/
namespace Kalai5.Cube3
open Set

noncomputable def SlabFamily.restrictFour {η : ℝ} (F : SlabFamily η (Fin 3 ⊕ Fin 2)) :
    SlabFamily η (Fin 3 ⊕ Unit) where
  point := Sum.elim (fun i => F.point (Sum.inl i)) (fun _ => F.point (Sum.inr 0))
  inj := by
    intro i j he
    rcases i with i | i <;> rcases j with j | j
    all_goals have hh := F.inj he
    all_goals simp_all
  extreme := by rintro (i | i); exact F.extreme (Sum.inl i); exact F.extreme (Sum.inr 0)
  positive := by rintro (i | i); exact F.positive (Sum.inl i); exact F.positive (Sum.inr 0)
  saturated := by rintro (i | i); exact F.saturated (Sum.inl i); exact F.saturated (Sum.inr 0)

lemma tripleSlab_three_four : Nonempty (SlabFamily 3 (Fin 3 ⊕ Unit)) := by
  let u := cycle3 1 1 1 0
  have hu : ∀ i,u i=1 ∨ u i= -1 := by intro i; fin_cases i <;> exact Or.inl rfl
  let G : SlabFamily 3 Unit :=
    { point := fun _ => (u,1)
      inj := fun _ _ _ => Subsingleton.elim _ _
      extreme := fun _ => tripleSlab_upper_cube hu (by norm_num) (by norm_num) (by norm_num)
        (by rw [cycle3_sum]; norm_num)
      positive := fun _ => by norm_num
      saturated := fun _ => ⟨0,Or.inl rfl⟩ }
  refine ⟨(upperThree (by norm_num : (1 : ℝ)<3)).sum G ?_⟩
  intro i j he
  have hh := congrArg Prod.snd he
  change (2 : ℝ)/(3+1)=1 at hh
  norm_num at hh

theorem tripleSlab_four {η : ℝ} (h1 : η ≠ 1) (hm1 : η ≠ -1) :
    Nonempty (SlabFamily η (Fin 3 ⊕ Unit)) := by
  by_cases h3 : η=3
  · rw [h3]; exact tripleSlab_three_four
  by_cases hm3 : η= -3
  · rw [hm3]
    obtain ⟨F⟩ := tripleSlab_three_four
    refine ⟨⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,?_⟩⟩
    · intro i
      rw [← tripleSlab_flip 3,← image_extremePoints]
      exact ⟨F.point i,F.extreme i,rfl⟩
    · intro i
      obtain ⟨j,hj | hj⟩ := F.saturated i
      · exact ⟨j,Or.inr (by change -(F.point i).1 j= -1; rw [hj])⟩
      · exact ⟨j,Or.inl (by change -(F.point i).1 j=1; rw [hj]; norm_num)⟩
  obtain ⟨F⟩ := tripleSlab_five h1 hm1 h3 hm3
  exact ⟨F.restrictFour⟩

end Kalai5.Cube3
