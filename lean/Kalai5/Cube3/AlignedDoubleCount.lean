import Kalai5.Cube3.MarkedDoubleFamilies

/-! Two distinct positive vertices marked by the same side of both intervals. -/

namespace Kalai5.Cube3
open Set

lemma doubleSlab_lower_two_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) (h2 : ¬(r=1 ∧ η=2)) :
    Nonempty (MarkedDoubleFamily r η (-1) (-1) (Fin 2)) := by
  let t := 2/(η+1-r)
  let u := 2/(η+r-1)
  have hd : 0 < η+1-r := by linarith
  have he : 0 < η+r-1 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  have hu1 : u ≤ 1 := (div_le_one he).2 (by linarith)
  have ht_eq : (η+(-1)*r+1)*t=1+1+(-1)+1 := by dsimp [t]; field_simp; ring
  have hu_eq : ((-η)+(-1)*r+1)*u=(-1)+(-1)+(-1)+1 := by dsimp [u]; field_simp; ring
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := -1)
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) ht ht1 (by linarith) ht_eq
  have hq' := doubleSlab_corner_point hr.le hr1 (s := -1) (v := -1) (σ := -1)
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) hu hu1 (by linarith) hu_eq
  let p := doublePoint 1 1 ((-1)*(1-r*t)) t
  let q := slabFlip (doublePoint (-1) (-1) ((-1)*(1-r*u)) u)
  have hq : q ∈ (doubleSlab r η).extremePoints ℝ := by
    have hq'' : q ∈ (doubleSlab r (-(-η))).extremePoints ℝ := by
      rw [← doubleSlab_flip r (-η),← image_extremePoints]
      exact ⟨_,hq',rfl⟩
    simpa only [neg_neg] using hq''
  have hrt : r*t < 1 := by
    by_cases h : r < 1
    · nlinarith
    · have hr' : r=1 := by linarith
      have hη : 2 < η := by
        have hne : η ≠ 2 := fun h => h2 ⟨hr',h⟩
        exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have ht' : t < 1 := (div_lt_one hd).2 (by linarith)
      rw [hr',one_mul]; exact ht'
  have hne : p ≠ q := by
    intro hh
    have hz := congrArg (fun z : SlabPoint => z.1 2) hh
    change (-1)*(1-r*t)= -((-1)*(1-r*u)) at hz
    have hru : r*u ≤ 1 := by nlinarith
    nlinarith
  let F := DoubleFamily.two p q hne hp hq ht hu
    ⟨0,Or.inl rfl⟩ ⟨0,Or.inl (by change -(-1 : ℝ)=1; ring)⟩
  refine ⟨⟨F,?_⟩⟩
  intro i; fin_cases i
  · left; change (-1)*((-1)*(1-r*t))+r*t=1; ring
  · right
    change slabForm η (-1) q=1
    have hh := slabForm_flip (-η) 1 (doublePoint (-1) (-1) ((-1)*(1-r*u)) u)
    rw [doubleSlab_corner_upper hu_eq] at hh
    simpa only [neg_neg] using hh

theorem doubleSlab_lower_two_nonneg {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : 0 ≤ η) (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
    Nonempty (MarkedDoubleFamily r η (-1) (-1) (Fin 2)) := by
  by_cases hlo : η ≤ 1-r
  · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; exact h0 ⟨he,by linarith⟩)
    have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η-r) (w := r-1)
      (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
    let F := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
      (by change 1 ≠ η-r; linarith)
    exact ⟨⟨F,fun i => Or.inr (doubleSlab_cap_lower (F.extreme i).1
      (DoubleFamily.swapped_height _ _ _ _ i))⟩⟩
  · by_cases hhi : η < 3-r
    · have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
        (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
      let F := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
        (by change 1 ≠ η+r-2; linarith)
      exact ⟨⟨F,fun i => Or.inr (doubleSlab_cap_lower (F.extreme i).1
        (DoubleFamily.swapped_height _ _ _ _ i))⟩⟩
    · exact doubleSlab_lower_two_high hr hr1 (by linarith) h2

theorem doubleSlab_aligned_two {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) (hm2 : ¬(r=1 ∧ η= -2)) :
    Nonempty (MarkedDoubleFamily r η 1 1 (Fin 2)) := by
  by_cases hη : 0 ≤ η
  · obtain ⟨G⟩ := doubleSlab_upper_four hr hr1 hη h0 h2
    exact ⟨(G.marked 1).reindex Sum.inl Sum.inl_injective⟩
  · obtain ⟨G⟩ := doubleSlab_lower_two_nonneg hr hr1 (show 0 ≤ -η by linarith)
      (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩)
      (by rintro ⟨hr,he⟩; exact hm2 ⟨hr,by linarith⟩)
    have h : Nonempty (MarkedDoubleFamily r (-(-η)) (-(-1)) (-(-1)) (Fin 2)) := ⟨G.flipped⟩
    simpa only [neg_neg] using h

end Kalai5.Cube3
