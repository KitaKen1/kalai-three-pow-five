import Kalai5.Cube3.BothWidthFamilies

/-! Four vertices saturating both positive-width intervals. -/
namespace Kalai5.Cube3
open Set

lemma doubleSlab_both_four_low {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : 0 ≤ η) (hlo : η ≤ 1-r) : Nonempty (BothDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := -1) (v := η+r) (w := 1-r)
    (Or.inr rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let F := BothDoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl) (by change 1 ≠ η-r; linarith)
    (doubleSlab_cap_both hr1.le (Or.inr rfl) (by ring))
  let G := BothDoubleFamily.swapped _ hq (by norm_num [doublePoint]) (Or.inr rfl) (by change -1 ≠ η+r; linarith)
    (doubleSlab_cap_both hr1.le (Or.inl rfl) (by ring))
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 2) he
  rw [BothDoubleFamily.swapped_third,BothDoubleFamily.swapped_third] at hh
  change r-1=1-r at hh
  linarith

noncomputable def bothOpposite {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) :
    BothDoubleFamily r η (Fin 2) := by
  have hd : 0 < η+1+r := by linarith
  have ht : 0 < 2/(η+1+r) := by positivity
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := -1) (σ := 1)
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) ht
    ((div_le_one hd).2 (by linarith)) (by linarith)
    (by field_simp; ring : (η+1*r+1)*(2/(η+1+r))=1+(-1)+1+1)
  exact BothDoubleFamily.swapped _ hp ht (Or.inl rfl) (by norm_num [doublePoint,cycle3])
    (doubleSlab_corner_both hr.le hr1 (Or.inl rfl) ht.le
      ((div_le_one hd).2 (by linarith))
      (by field_simp; ring : (η+1*r+1)*(2/(η+1+r))=1+(-1)+1+1))

lemma bothOpposite_height {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) (i : Fin 2) :
    ((bothOpposite hr hr1 hη).point i).2=2/(η+1+r) := by
  fin_cases i <;> rfl

lemma bothOpposite_sum {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) (i : Fin 2) :
    ((bothOpposite hr hr1 hη).point i).1 0+((bothOpposite hr hr1 hη).point i).1 1=0 := by
  fin_cases i <;> norm_num [bothOpposite,BothDoubleFamily.swapped,DoubleFamily.swapped,DoubleFamily.two,doublePoint,cycle3,doubleSwap]

lemma doubleSlab_both_four_middle {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hlo : 1-r < η) (hhi : η < 3-r) : Nonempty (BothDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let G := BothDoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl) (by change 1 ≠ η+r-2; linarith)
    (doubleSlab_cap_both hr1 (Or.inl rfl) (by ring))
  refine ⟨(bothOpposite hr hr1 hlo).sum G ?_⟩
  intro i j he
  have hh := congrArg Prod.snd he
  rw [bothOpposite_height,BothDoubleFamily.swapped_height] at hh
  change 2/(η+1+r)=1 at hh
  have hlt : 2/(η+1+r)<1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

lemma doubleSlab_both_four_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) (hne : ¬(r=1 ∧ η=2)) : Nonempty (BothDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hplus : 0 < η+1+r := by linarith
  have hminus : 0 < η+1-r := by linarith
  have hmid : 1-r < η := by linarith
  have hdiff : 4/(η+1+r) ≠ 2/(η+1-r) := by
    intro hh
    have hh := (div_eq_div_iff hplus.ne' hminus.ne').1 hh
    apply hne
    constructor <;> linarith
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := 1)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by positivity : 0 < 4/(η+1+r))
    ((div_le_one hplus).2 (by linarith)) (by linarith)
    (by field_simp; ring : (η+1*r+1)*(4/(η+1+r))=1+1+1+1)
  have hq := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := -1)
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (by positivity : 0 < 2/(η+1-r))
    ((div_le_one hminus).2 (by linarith)) (by linarith)
    (by field_simp; ring : (η+(-1)*r+1)*(2/(η+1-r))=1+1+(-1)+1)
  let G := BothDoubleFamily.two _ _ (fun he => hdiff (congrArg Prod.snd he)) hp hq
    (by change 0 < 4/(η+1+r); positivity) (by change 0 < 2/(η+1-r); positivity)
    ⟨0,Or.inl rfl⟩ ⟨0,Or.inl rfl⟩
    (doubleSlab_corner_both hr.le hr1 (Or.inl rfl) (by positivity)
      ((div_le_one hplus).2 (by linarith))
      (by field_simp; ring : (η+1*r+1)*(4/(η+1+r))=1+1+1+1))
    (doubleSlab_corner_both hr.le hr1 (Or.inr rfl) (by positivity)
      ((div_le_one hminus).2 (by linarith))
      (by field_simp; ring : (η+(-1)*r+1)*(2/(η+1-r))=1+1+(-1)+1))
  refine ⟨(bothOpposite hr hr1 hmid).sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 0+p.1 1) he
  rw [bothOpposite_sum] at hh
  fin_cases j <;> norm_num [G,BothDoubleFamily.two,DoubleFamily.two,doublePoint,cycle3] at hh

theorem doubleSlab_both_four {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) (hm2 : ¬(r=1 ∧ η= -2)) :
    Nonempty (BothDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hnonneg (η : ℝ) (hη : 0 ≤ η) (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
      Nonempty (BothDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
    by_cases hlo : η ≤ 1-r
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; apply h0; exact ⟨he,by linarith⟩)
      exact doubleSlab_both_four_low hr hrlt hη hlo
    · by_cases hhi : η < 3-r
      · exact doubleSlab_both_four_middle hr hr1 (by linarith) hhi
      · exact doubleSlab_both_four_high hr hr1 (by linarith) h2
  by_cases hη : 0 ≤ η
  · exact hnonneg η hη h0 h2
  obtain ⟨F⟩ := hnonneg (-η) (by linarith) (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩)
    (by rintro ⟨hr,he⟩; exact hm2 ⟨hr,by linarith⟩)
  refine ⟨{ toDoubleFamily := ⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,?_⟩
            both := ?_ }⟩
  · intro i
    have he : slabFlip '' doubleSlab r (-η)=doubleSlab r η := by simpa using doubleSlab_flip r (-η)
    rw [← he,← image_extremePoints]; exact ⟨F.point i,F.extreme i,rfl⟩
  · intro i
    obtain ⟨j,hj | hj⟩ := F.saturated i
    · exact ⟨j,Or.inr (by change -(F.point i).1 j.castSucc= -1; rw [hj])⟩
    · exact ⟨j,Or.inl (by change -(F.point i).1 j.castSucc=1; rw [hj]; norm_num)⟩

  · intro i
    simpa using (F.both i).flip

end Kalai5.Cube3
