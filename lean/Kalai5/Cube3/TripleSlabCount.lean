import Kalai5.Cube3.TripleSlab

/-! Five positive vertices away from the four exceptional drift values. -/

namespace Kalai5.Cube3

open Set

lemma cycle3_sum (a b c : ℝ) (i : Fin 3) : ∑ j, cycle3 a b c i j = a+b+c := by
  fin_cases i <;> simp [cycle3,Fin.sum_univ_three] <;> ring

lemma cycle3_has_sign {a b c : ℝ} (ha : a = 1 ∨ a = -1) (i : Fin 3) :
    ∃ j, cycle3 a b c i j = 1 ∨ cycle3 a b c i j = -1 := by
  fin_cases i
  · exact ⟨0,ha⟩
  · exact ⟨1,ha⟩
  · exact ⟨2,ha⟩

structure SlabFamily (η : ℝ) (ι : Type*) where
  point : ι → SlabPoint
  inj : Function.Injective point
  extreme : ∀ i, point i ∈ (tripleSlab η).extremePoints ℝ
  positive : ∀ i, 0 < (point i).2
  saturated : ∀ i, ∃ j, (point i).1 j = 1 ∨ (point i).1 j = -1

namespace SlabFamily

noncomputable def sum {η : ℝ} {ι κ : Type*} (F : SlabFamily η ι) (G : SlabFamily η κ)
    (hdis : ∀ i j, F.point i ≠ G.point j) : SlabFamily η (ι ⊕ κ) where
  point := Sum.elim F.point G.point
  inj := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (F.inj h)
    · exact (hdis i j h).elim
    · exact (hdis j i h.symm).elim
    · exact congrArg Sum.inr (G.inj h)
  extreme := by rintro (i | i); exact F.extreme i; exact G.extreme i
  positive := by rintro (i | i); exact F.positive i; exact G.positive i
  saturated := by rintro (i | i); exact F.saturated i; exact G.saturated i

def firstTwo (i : Fin 2) : Fin 3 := ⟨i.val,by omega⟩

lemma firstTwo_injective : Function.Injective firstTwo := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 3 => k.val) h)

noncomputable def restrictTwo {η : ℝ} (F : SlabFamily η (Fin 3)) : SlabFamily η (Fin 2) where
  point i := F.point (firstTwo i)
  inj := F.inj.comp firstTwo_injective
  extreme i := F.extreme (firstTwo i)
  positive i := F.positive (firstTwo i)
  saturated i := F.saturated (firstTwo i)

noncomputable def capCycle {a b c η : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : |c| ≤ 1) (hs : a+b+c=η) (hi : a ≠ b ∨ b ≠ c) : SlabFamily η (Fin 3) where
  point i := (cycle3 a b c i,1)
  inj := by intro i j h; exact cycle3_injective hi (congrArg Prod.fst h)
  extreme i := tripleSlab_cap (cycle3_extreme a b c η ha hb hc hs i)
  positive _ := by norm_num
  saturated i := cycle3_has_sign ha i

end SlabFamily

lemma tripleSlab_upper_cube {η t : ℝ} {u : E 3}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : η+1 ≠ 0) (he : (η+1)*t = 1 + ∑ i, u i) :
    (u,t) ∈ (tripleSlab η).extremePoints ℝ := by
  have hr : η*t - ∑ i, u i = 1-t := by nlinarith [he]
  refine tripleSlab_cube (σ := 1) ?_ hu (by norm_num) (by simpa using hc) ?_
  · refine ⟨fun i => ?_,?_⟩
    · rcases hu i with h | h <;> rw [h] <;> norm_num
    · change |η*t - ∑ i, u i| + |t| ≤ 1
      rw [hr,abs_of_nonneg (by linarith),abs_of_pos ht]
      linarith
  · change 1 * (η*t - ∑ i, u i) + t = 1
    rw [hr]; ring

lemma tripleSlab_lower_cube {η t : ℝ} {u : E 3}
    (hu : ∀ i, u i = 1 ∨ u i = -1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hc : η-1 ≠ 0) (he : (η-1)*t = (∑ i, u i) - 1) :
    (u,t) ∈ (tripleSlab η).extremePoints ℝ := by
  have hr : η*t - ∑ i, u i = t-1 := by nlinarith [he]
  refine tripleSlab_cube (σ := -1) ?_ hu (by norm_num) (by intro h; apply hc; linarith) ?_
  · refine ⟨fun i => ?_,?_⟩
    · rcases hu i with h | h <;> rw [h] <;> norm_num
    · change |η*t - ∑ i, u i| + |t| ≤ 1
      rw [hr,abs_of_nonpos (by linarith),abs_of_pos ht]
      linarith
  · change -1 * (η*t - ∑ i, u i) + t = 1
    rw [hr]; ring

noncomputable def upperThree {η : ℝ} (hη : 1 < η) : SlabFamily η (Fin 3) where
  point i := (cycle3 1 1 (-1) i,2/(η+1))
  inj := by intro i j h; exact cycle3_injective (Or.inr (by norm_num)) (congrArg Prod.fst h)
  extreme i := by
    apply tripleSlab_upper_cube
    · intro j; fin_cases i <;> fin_cases j <;> norm_num [cycle3]
    · positivity
    · apply (div_le_one (by linarith : 0 < η+1)).2; linarith
    · linarith
    · rw [cycle3_sum]; field_simp; ring
  positive _ := by positivity
  saturated i := cycle3_has_sign (Or.inl rfl) i

lemma tripleSlab_five_low {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) :
    Nonempty (SlabFamily η (Fin 3 ⊕ Fin 2)) := by
  let F := SlabFamily.capCycle (a := 1) (b := -1) (c := η)
    (Or.inl rfl) (Or.inr rfl) (by rw [abs_of_nonneg h0]; exact h1.le)
    (by ring) (Or.inl (by norm_num))
  let G := SlabFamily.capCycle (a := -1) (b := 1) (c := η)
    (Or.inr rfl) (Or.inl rfl) (by rw [abs_of_nonneg h0]; exact h1.le)
    (by ring) (Or.inl (by norm_num))
  refine ⟨F.sum G.restrictTwo ?_⟩
  intro i j h
  have he := congrArg Prod.fst h
  exact cycle3_swap_ne (by norm_num : (1 : ℝ) ≠ -1) (by linarith) (by linarith)
    i (SlabFamily.firstTwo j) he

lemma tripleSlab_five_middle {η : ℝ} (h1 : 1 < η) (h3 : η < 3) :
    Nonempty (SlabFamily η (Fin 3 ⊕ Fin 2)) := by
  let F := SlabFamily.capCycle (a := 1) (b := 1) (c := η-2)
    (Or.inl rfl) (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩)
    (by ring) (Or.inr (by linarith))
  refine ⟨F.sum (upperThree h1).restrictTwo ?_⟩
  intro i j he
  have ht : 1 = 2/(η+1) := congrArg Prod.snd he
  have hh : 2/(η+1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

lemma tripleSlab_five_high {η : ℝ} (h3 : 3 < η) :
    Nonempty (SlabFamily η (Fin 3 ⊕ Fin 2)) := by
  let u := cycle3 1 1 1 0
  have hu : ∀ i, u i = 1 ∨ u i = -1 := by intro i; fin_cases i <;> simp [u,cycle3]
  have hsum : ∑ i, u i = 3 := by rw [cycle3_sum]; norm_num
  have hp : 0 < η+1 := by linarith
  have hm : 0 < η-1 := by linarith
  have hne : 4/(η+1) ≠ 2/(η-1) := by
    intro h
    have h := (div_eq_div_iff hp.ne' hm.ne').1 h
    linarith
  let G : SlabFamily η (Fin 2) :=
    { point := fun i => (u,(![4/(η+1),2/(η-1)] : Fin 2 → ℝ) i)
      inj := by
        intro i j h
        have he := congrArg Prod.snd h
        fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at he
        all_goals first | rfl | exact (hne he).elim | exact (hne he.symm).elim
      extreme := by
        intro i
        fin_cases i
        · apply tripleSlab_upper_cube hu (by positivity) ((div_le_one hp).2 (by linarith)) hp.ne'
          rw [hsum]; field_simp; ring
        · apply tripleSlab_lower_cube hu (by positivity) ((div_le_one hm).2 (by linarith)) hm.ne'
          rw [hsum]; field_simp; ring
      positive := by intro i; fin_cases i <;> dsimp <;> positivity
      saturated := fun _ => ⟨0,Or.inl rfl⟩ }
  refine ⟨(upperThree (by linarith : 1 < η)).sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => ∑ k, p.1 k) he
  change (∑ k, cycle3 1 1 (-1) i k) = ∑ k, u k at hh
  rw [cycle3_sum,hsum] at hh
  norm_num at hh

lemma tripleSlab_five_nonnegative {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≠ 1) (h3 : η ≠ 3) :
    Nonempty (SlabFamily η (Fin 3 ⊕ Fin 2)) := by
  rcases lt_or_gt_of_ne h1 with h | h
  · exact tripleSlab_five_low h0 h
  · rcases lt_or_gt_of_ne h3 with h' | h'
    · exact tripleSlab_five_middle h h'
    · exact tripleSlab_five_high h'

theorem tripleSlab_five {η : ℝ} (h1 : η ≠ 1) (hm1 : η ≠ -1)
    (h3 : η ≠ 3) (hm3 : η ≠ -3) : Nonempty (SlabFamily η (Fin 3 ⊕ Fin 2)) := by
  by_cases h0 : 0 ≤ η
  · exact tripleSlab_five_nonnegative h0 h1 h3
  obtain ⟨F⟩ := tripleSlab_five_nonnegative (by linarith : 0 ≤ -η)
    (by intro h; apply hm1; linarith) (by intro h; apply hm3; linarith)
  refine ⟨⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,?_⟩⟩
  · intro i
    have he : slabFlip '' tripleSlab (-η) = tripleSlab η := by simpa using tripleSlab_flip (-η)
    rw [← he,← image_extremePoints]
    exact ⟨F.point i,F.extreme i,rfl⟩
  · intro i
    obtain ⟨j,hj | hj⟩ := F.saturated i
    · exact ⟨j,Or.inr (by change -(F.point i).1 j = -1; rw [hj])⟩
    · exact ⟨j,Or.inl (by change -(F.point i).1 j = 1; rw [hj]; norm_num)⟩

end Kalai5.Cube3
