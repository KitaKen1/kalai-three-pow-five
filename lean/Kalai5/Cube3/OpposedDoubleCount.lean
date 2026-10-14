import Kalai5.Cube3.MarkedDoubleFamilies

/-! Three positive vertices marked by opposite interval sides, with all drift signs. -/

namespace Kalai5.Cube3
open Set

lemma doubleSlab_opposed_low {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : 0 ≤ η) (hlo : η ≤ 1-r) :
    Nonempty (MarkedDoubleFamily r η 1 (-1) (Fin 2 ⊕ Unit)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := -1) (v := η+r) (w := 1-r)
    (Or.inr rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let B := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl) (by change 1 ≠ η-r; linarith)
  let F : MarkedDoubleFamily r η 1 (-1) (Fin 2) :=
    ⟨B,fun i => Or.inr (doubleSlab_cap_lower (B.extreme i).1
      (DoubleFamily.swapped_height _ _ _ _ i))⟩
  let G := MarkedDoubleFamily.one _ hq (by norm_num [doublePoint]) ⟨0,Or.inr rfl⟩
    (Or.inr (doubleSlab_cap_lower hq.1 rfl) : widthForm r 1 _=1 ∨ slabForm η (-1) _=1)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 2) he
  change (B.point i).1 2=1-r at hh
  rw [DoubleFamily.swapped_third] at hh
  change r-1=1-r at hh; linarith

lemma doubleSlab_opposed_middle {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hlo : 1-r < η) (hhi : η < 3-r) :
    Nonempty (MarkedDoubleFamily r η 1 (-1) (Fin 2 ⊕ Unit)) := by
  have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let G := MarkedDoubleFamily.one _ hp (by norm_num [doublePoint]) ⟨0,Or.inl rfl⟩
    (Or.inr (doubleSlab_cap_lower hp.1 rfl) : widthForm r 1 _=1 ∨ slabForm η (-1) _=1)
  refine ⟨(MarkedDoubleFamily.opposite hr hr1 hlo).sum G ?_⟩
  intro i j he
  have hh := congrArg Prod.snd he
  change ((doubleOpposite hr hr1 hlo).point i).2=1 at hh
  rw [doubleOpposite_height] at hh
  have hlt : 2/(η+1+r)<1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

lemma doubleSlab_opposed_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) : Nonempty (MarkedDoubleFamily r η 1 (-1) (Fin 2 ⊕ Unit)) := by
  have hplus : 0 < η+1+r := by linarith
  have hmid : 1-r < η := by linarith
  have heq : (η+1*r+1)*(4/(η+1+r))=1+1+1+1 := by field_simp; ring
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := 1)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by positivity : 0 < 4/(η+1+r))
    ((div_le_one hplus).2 (by linarith)) (by linarith) heq
  have hwidth : widthForm r 1 (doublePoint 1 1 (1*(1-r*(4/(η+1+r)))) (4/(η+1+r)))=1 := by
    change 1*(1*(1-r*(4/(η+1+r))))+r*(4/(η+1+r))=1; ring
  let G := MarkedDoubleFamily.one _ hp (by change 0 < 4/(η+1+r); positivity)
    ⟨0,Or.inl rfl⟩ (Or.inl hwidth : widthForm r 1 _=1 ∨ slabForm η (-1) _=1)
  refine ⟨(MarkedDoubleFamily.opposite hr hr1 hmid).sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 0+p.1 1) he
  change ((doubleOpposite hr hr1 hmid).point i).1 0+
    ((doubleOpposite hr hr1 hmid).point i).1 1=1+1 at hh
  rw [doubleOpposite_sum] at hh; norm_num at hh

theorem doubleSlab_opposed_nonneg {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 ≤ η)
    (h0 : ¬(r=1 ∧ η=0)) : Nonempty (MarkedDoubleFamily r η 1 (-1) (Fin 2 ⊕ Unit)) := by
  by_cases hlo : η ≤ 1-r
  · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; apply h0; exact ⟨he,by linarith⟩)
    exact doubleSlab_opposed_low hr hrlt hη hlo
  · by_cases hhi : η < 3-r
    · exact doubleSlab_opposed_middle hr hr1 (by linarith) hhi
    · exact doubleSlab_opposed_high hr hr1 (by linarith)

theorem doubleSlab_opposed_three {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) (hm2 : ¬(r=1 ∧ η= -2)) :
    Nonempty (MarkedDoubleFamily r η 1 (-1) (Fin 2 ⊕ Unit)) := by
  by_cases hη : 0 ≤ η
  · exact doubleSlab_opposed_nonneg hr hr1 hη h0
  obtain ⟨G⟩ := doubleSlab_upper_four hr hr1 (show 0 ≤ -η by linarith)
    (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩)
    (by rintro ⟨hr,he⟩; exact hm2 ⟨hr,by linarith⟩)
  have h : Nonempty (MarkedDoubleFamily r (-(-η)) (-(-1)) (-1) (Fin 2 ⊕ Unit)) :=
    ⟨((G.marked (-1)).reindex selectThree selectThree_injective).flipped⟩
  simpa only [neg_neg] using h

theorem doubleSlab_opposed_three_reverse {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
    Nonempty (MarkedDoubleFamily r η (-1) 1 (Fin 2 ⊕ Unit)) := by
  obtain ⟨G⟩ := doubleSlab_opposed_three hr hr1
    (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩ : ¬(r=1 ∧ -η=0))
    (by rintro ⟨hr,he⟩; exact h2 ⟨hr,by linarith⟩ : ¬(r=1 ∧ -η= -2))
  have h : Nonempty (MarkedDoubleFamily r (-(-η)) (-1) (-(-1)) (Fin 2 ⊕ Unit)) := ⟨G.flipped⟩
  simpa only [neg_neg] using h

end Kalai5.Cube3
