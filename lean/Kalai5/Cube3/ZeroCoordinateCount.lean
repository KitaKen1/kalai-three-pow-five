import Kalai5.Cube3.ZeroCoordinateCap

/-! Three positive slice vertices saturating one prescribed zero-width coordinate. -/
namespace Kalai5.Cube3
open Set

structure ZeroDoubleFamily (r η : ℝ) (ι : Type*) extends DoubleFamily r η ι where
  zero_saturated : ∀ i,(point i).1 0=1 ∨ (point i).1 0= -1

namespace ZeroDoubleFamily

noncomputable def sum {r η : ℝ} {ι κ : Type*} (F : ZeroDoubleFamily r η ι)
    (G : ZeroDoubleFamily r η κ) (hd : ∀ i j,F.point i ≠ G.point j) : ZeroDoubleFamily r η (ι ⊕ κ) where
  toDoubleFamily := F.toDoubleFamily.sum G.toDoubleFamily hd
  zero_saturated := by rintro (i | i); exact F.zero_saturated i; exact G.zero_saturated i

noncomputable def one {r η : ℝ} (p : SlabPoint)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (ht : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) : ZeroDoubleFamily r η Unit where
  point _ := p
  inj _ _ _ := Subsingleton.elim _ _
  extreme _ := hp
  positive _ := ht
  saturated _ := ⟨0,hs⟩
  zero_saturated _ := hs

noncomputable def flipped {r η : ℝ} {ι : Type*} (F : ZeroDoubleFamily r η ι) :
    ZeroDoubleFamily r (-η) ι where
  point i := slabFlip (F.point i)
  inj := slabFlip.injective.comp F.inj
  extreme := by
    intro i
    rw [← doubleSlab_flip r η,← image_extremePoints]
    exact ⟨F.point i,F.extreme i,rfl⟩
  positive := F.positive
  saturated := by
    intro i
    refine ⟨0,?_⟩
    change -(F.point i).1 0=1 ∨ -(F.point i).1 0= -1
    rcases F.zero_saturated i with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; norm_num)
  zero_saturated := by
    intro i
    change -(F.point i).1 0=1 ∨ -(F.point i).1 0= -1
    rcases F.zero_saturated i with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; norm_num)

noncomputable def opposite {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) :
    ZeroDoubleFamily r η (Fin 2) where
  toDoubleFamily := doubleOpposite hr hr1 hη
  zero_saturated := by
    intro i; fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl

end ZeroDoubleFamily

theorem doubleSlab_zero_three_low {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : 0 ≤ η) (hlo : η ≤ 1-r) : Nonempty (ZeroDoubleFamily r η (Fin 2 ⊕ Unit)) := by
  have hp := doubleSlab_zero_cap (show |η|+r≤1 by rw [abs_of_nonneg hη]; linarith)
  let B := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
    (by norm_num [doublePoint,cycle3])
  let F : ZeroDoubleFamily r η (Fin 2) := ⟨B,by
    intro i; fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl⟩
  have hq := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  let G := ZeroDoubleFamily.one _ hq (by norm_num [doublePoint]) (Or.inl rfl)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hz := congrArg (fun p : SlabPoint => p.1 2) he
  change (B.point i).1 2=r-1 at hz
  have hthird : (B.point i).1 2=η := by fin_cases i <;> rfl
  linarith

theorem doubleSlab_zero_three_middle {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hlo : 1-r < η) (hhi : η < 3-r) : Nonempty (ZeroDoubleFamily r η (Fin 2 ⊕ Unit)) := by
  let F := ZeroDoubleFamily.opposite hr hr1 hlo
  have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let G := ZeroDoubleFamily.one _ hp (by norm_num [doublePoint]) (Or.inl rfl)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hz := congrArg Prod.snd he
  change ((doubleOpposite hr hr1 hlo).point i).2=1 at hz
  rw [doubleOpposite_height] at hz
  have ht : 2/(η+1+r)<1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

theorem doubleSlab_zero_three_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) : Nonempty (ZeroDoubleFamily r η (Fin 2 ⊕ Unit)) := by
  have hmid : 1-r < η := by linarith
  have hplus : 0 < η+1+r := by linarith
  let F := ZeroDoubleFamily.opposite hr hr1 hmid
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := 1)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by positivity : 0 < 4/(η+1+r))
    ((div_le_one (by linarith)).2 (by linarith)) (by linarith)
    (by field_simp; ring : (η+1*r+1)*(4/(η+1+r))=1+1+1+1)
  let G := ZeroDoubleFamily.one _ hp (by change 0 < 4/(η+1+r); positivity) (Or.inl rfl)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hz := congrArg (fun p : SlabPoint => p.1 0+p.1 1) he
  change ((doubleOpposite hr hr1 hmid).point i).1 0+
    ((doubleOpposite hr hr1 hmid).point i).1 1=1+1 at hz
  rw [doubleOpposite_sum] at hz; norm_num at hz

theorem doubleSlab_zero_three {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) : Nonempty (ZeroDoubleFamily r η (Fin 2 ⊕ Unit)) := by
  have hnonneg (η : ℝ) (hη : 0 ≤ η) (h0 : ¬(r=1 ∧ η=0)) :
      Nonempty (ZeroDoubleFamily r η (Fin 2 ⊕ Unit)) := by
    by_cases hlo : η ≤ 1-r
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; exact h0 ⟨he,by linarith⟩)
      exact doubleSlab_zero_three_low hr hrlt hη hlo
    · by_cases hhi : η < 3-r
      · exact doubleSlab_zero_three_middle hr hr1 (by linarith) hhi
      · exact doubleSlab_zero_three_high hr hr1 (by linarith)
  by_cases hη : 0 ≤ η
  · exact hnonneg η hη h0
  obtain ⟨F⟩ := hnonneg (-η) (by linarith) (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩)
  have hh := F.flipped
  simpa only [neg_neg] using (show Nonempty (ZeroDoubleFamily r (-(-η)) (Fin 2 ⊕ Unit)) from ⟨hh⟩)

end Kalai5.Cube3
