import Kalai5.Cube3.AlignedCentralCount

/-! Unequal widths give three marked vertices as soon as the common support is nonnegative. -/
namespace Kalai5.Cube3
open Set

lemma doubleSlab_lower_three_middle {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hlo : 1-r < η) (hhi : η ≤ 1+r) :
    Nonempty (MarkedDoubleFamily r η (-1) (-1) (Fin 2 ⊕ Unit)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  let B := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
    (by change 1 ≠ η+r-2; linarith)
  let F : MarkedDoubleFamily r η (-1) (-1) (Fin 2) :=
    ⟨B,fun i => Or.inr (doubleSlab_cap_lower (B.extreme i).1
      (DoubleFamily.swapped_height _ _ _ _ i))⟩
  let G := MarkedDoubleFamily.one _ hq (by norm_num [doublePoint]) ⟨0,Or.inl rfl⟩
    (Or.inr (doubleSlab_cap_lower hq.1 rfl) : widthForm r (-1) _=1 ∨ slabForm η (-1) _=1)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hz := congrArg (fun p : SlabPoint => p.1 2) he
  change (B.point i).1 2=r-1 at hz
  rw [DoubleFamily.swapped_third] at hz
  change 1-r=r-1 at hz; linarith

theorem doubleSlab_aligned_three_unequal {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : -1-r ≤ η) : Nonempty (MarkedDoubleFamily r η 1 1 (Fin 2 ⊕ Unit)) := by
  by_cases hc : r-1 ≤ η
  · obtain ⟨F⟩ := doubleSlab_upper_four_above hr hr1.le hc
      (by rintro ⟨he,_⟩; linarith) (by rintro ⟨he,_⟩; linarith)
    exact ⟨(F.marked 1).reindex selectThree selectThree_injective⟩
  · obtain ⟨F⟩ := doubleSlab_lower_three_middle hr hr1
      (show 1-r < -η by linarith) (show -η ≤ 1+r by linarith)
    have h : Nonempty (MarkedDoubleFamily r (-(-η)) (-(-1)) (-(-1)) (Fin 2 ⊕ Unit)) := ⟨F.flipped⟩
    simpa only [neg_neg] using h

variable {x : Fin 8 → E5} {C : Config x}

theorem TwoWidthSlice.aligned_three_unequal (F : TwoWidthSlice C)
    (A : SliceEdge F (F.order 2) 1) (B : SliceEdge F (F.order 3) 1)
    (hr : F.ratio < 1) (hη : -1-F.ratio ≤ F.eta)
    {n : E 2} (hn : ‖n‖=1) {a : ℝ} (ha : 0 < a) (he : F.normal=a • n) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Unit),∀ k,H.normal k=n := by
  obtain ⟨G⟩ := doubleSlab_aligned_three_unequal F.ratio_pos hr hη
  exact F.marked_family G A B hn ha he

end Kalai5.Cube3
