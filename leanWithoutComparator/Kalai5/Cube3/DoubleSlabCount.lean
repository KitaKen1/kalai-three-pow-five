import Kalai5.Cube3.DoubleSlab

/-! Four positive vertices, including the transition values of the width ratio. -/

namespace Kalai5.Cube3
open Set

noncomputable def doublePoint (a b c t : ℝ) : SlabPoint := (cycle3 a b c 0,t)

structure DoubleFamily (r η : ℝ) (ι : Type*) where
  point : ι → SlabPoint
  inj : Function.Injective point
  extreme : ∀ i, point i ∈ (doubleSlab r η).extremePoints ℝ
  positive : ∀ i, 0 < (point i).2
  saturated : ∀ i, ∃ j : Fin 2, (point i).1 j.castSucc=1 ∨ (point i).1 j.castSucc= -1

namespace DoubleFamily

noncomputable def sum {r η : ℝ} {ι κ : Type*} (F : DoubleFamily r η ι)
    (G : DoubleFamily r η κ) (hd : ∀ i j,F.point i ≠ G.point j) : DoubleFamily r η (ι ⊕ κ) where
  point := Sum.elim F.point G.point
  inj := sum_family_injective _ _ F.inj G.inj hd
  extreme := by rintro (i | i); exact F.extreme i; exact G.extreme i
  positive := by rintro (i | i); exact F.positive i; exact G.positive i
  saturated := by rintro (i | i); exact F.saturated i; exact G.saturated i

noncomputable def two {r η : ℝ} (p q : SlabPoint) (hne : p ≠ q)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hq : q ∈ (doubleSlab r η).extremePoints ℝ)
    (hpt : 0 < p.2) (hqt : 0 < q.2)
    (hps : ∃ j : Fin 2,p.1 j.castSucc=1 ∨ p.1 j.castSucc= -1)
    (hqs : ∃ j : Fin 2,q.1 j.castSucc=1 ∨ q.1 j.castSucc= -1) : DoubleFamily r η (Fin 2) where
  point := ![p,q]
  inj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  extreme := by intro i; fin_cases i <;> assumption
  positive := by intro i; fin_cases i <;> assumption
  saturated := by intro i; fin_cases i <;> assumption

noncomputable def swapped {r η : ℝ} (p : SlabPoint)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1) : DoubleFamily r η (Fin 2) :=
  two p (doubleSwap p) (fun he => hne (congrArg (fun z => z.1 0) he)) hp
    (by rw [← doubleSlab_swap r η,← image_extremePoints]; exact ⟨p,hp,rfl⟩)
    hpt hpt ⟨0,hs⟩ ⟨1,hs⟩

lemma swapped_height {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1) (i : Fin 2) :
    ((swapped p hp hpt hs hne).point i).2=p.2 := by fin_cases i <;> rfl

lemma swapped_third {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1) (i : Fin 2) :
    ((swapped p hp hpt hs hne).point i).1 2=p.1 2 := by fin_cases i <;> rfl

lemma swapped_sum {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1) (i : Fin 2) :
    ((swapped p hp hpt hs hne).point i).1 0+
      ((swapped p hp hpt hs hne).point i).1 1=p.1 0+p.1 1 := by
  fin_cases i
  · rfl
  · exact add_comm _ _

end DoubleFamily

lemma doubleSlab_cap_point {r η s v w : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : s=1 ∨ s= -1) (hv : |v|≤1) (hw : w=1-r ∨ w=r-1)
    (he : η=s+v+w) : doublePoint s v w 1 ∈ (doubleSlab r η).extremePoints ℝ := by
  obtain ⟨σ,hσ,hσw⟩ : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧ σ*w+r=1 := by
    rcases hw with hw | hw
    · exact ⟨1,Or.inl rfl,by rw [hw]; ring⟩
    · exact ⟨-1,Or.inr rfl,by rw [hw]; ring⟩
  apply doubleSlab_cap hr hσ (ht := rfl) (h0 := hs)
    (hw := by change σ*w+r*1=1; simpa using hσw)
  refine ⟨?_,hv,?_,?_⟩
  · change |s|≤1; rcases hs with rfl | rfl <;> norm_num
  · change |w|+r*|1|≤1
    rcases hw with rfl | rfl
    · rw [abs_of_nonneg (by linarith)]; norm_num
    · rw [abs_of_nonpos (by linarith)]; norm_num
  · change |η*1-∑ i,cycle3 s v w 0 i|+|1|≤1
    rw [cycle3_sum,he]; norm_num

lemma doubleSlab_corner_point {r η s v σ t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : s=1 ∨ s= -1) (hv : v=1 ∨ v= -1) (hσ : σ=1 ∨ σ= -1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hc : η+σ*r+1 ≠ 0)
    (he : (η+σ*r+1)*t=s+v+σ+1) :
    doublePoint s v (σ*(1-r*t)) t ∈ (doubleSlab r η).extremePoints ℝ := by
  have hw : 0 ≤ 1-r*t := by nlinarith
  have hlast : η*t-(s+v+σ*(1-r*t))=1-t := by nlinarith [he]
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  apply doubleSlab_corner hr hσ (h0 := hs) (h1 := hv) (hc := hc)
  · refine ⟨?_,?_,?_,?_⟩
    · change |s|≤1; rcases hs with rfl | rfl <;> norm_num
    · change |v|≤1; rcases hv with rfl | rfl <;> norm_num
    · change |σ*(1-r*t)|+r*|t|≤1
      rw [abs_mul,hσabs,one_mul,abs_of_nonneg hw,abs_of_pos ht]; linarith
    · change |η*t-∑ i,cycle3 s v (σ*(1-r*t)) 0 i|+|t|≤1
      rw [cycle3_sum,hlast,abs_of_nonneg (by linarith),abs_of_pos ht]; linarith
  · change σ*(σ*(1-r*t))+r*t=1
    rcases hσ with rfl | rfl <;> ring
  · change 1*(η*t-∑ i,cycle3 s v (σ*(1-r*t)) 0 i)+t=1
    rw [cycle3_sum,hlast]; ring

lemma doubleSlab_four_low {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : 0 ≤ η) (hlo : η ≤ 1-r) : Nonempty (DoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := -1) (v := η+r) (w := 1-r)
    (Or.inr rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let F := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl) (by change 1 ≠ η-r; linarith)
  let G := DoubleFamily.swapped _ hq (by norm_num [doublePoint]) (Or.inr rfl) (by change -1 ≠ η+r; linarith)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 2) he
  rw [DoubleFamily.swapped_third,DoubleFamily.swapped_third] at hh
  change r-1=1-r at hh
  linarith

noncomputable def doubleOpposite {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) :
    DoubleFamily r η (Fin 2) := by
  have hd : 0 < η+1+r := by linarith
  have ht : 0 < 2/(η+1+r) := by positivity
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := -1) (σ := 1)
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) ht
    ((div_le_one hd).2 (by linarith)) (by linarith)
    (by field_simp; ring : (η+1*r+1)*(2/(η+1+r))=1+(-1)+1+1)
  exact DoubleFamily.swapped _ hp ht (Or.inl rfl) (by norm_num [doublePoint,cycle3])

lemma doubleOpposite_height {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) (i : Fin 2) :
    ((doubleOpposite hr hr1 hη).point i).2=2/(η+1+r) := by
  fin_cases i <;> rfl

lemma doubleOpposite_sum {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) (i : Fin 2) :
    ((doubleOpposite hr hr1 hη).point i).1 0+((doubleOpposite hr hr1 hη).point i).1 1=0 := by
  fin_cases i <;> norm_num [doubleOpposite,DoubleFamily.swapped,DoubleFamily.two,doublePoint,cycle3,doubleSwap]

lemma doubleSlab_four_middle {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hlo : 1-r < η) (hhi : η < 3-r) : Nonempty (DoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let G := DoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl) (by change 1 ≠ η+r-2; linarith)
  refine ⟨(doubleOpposite hr hr1 hlo).sum G ?_⟩
  intro i j he
  have hh := congrArg Prod.snd he
  rw [doubleOpposite_height,DoubleFamily.swapped_height] at hh
  change 2/(η+1+r)=1 at hh
  have hlt : 2/(η+1+r)<1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

lemma doubleSlab_four_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) (hne : ¬(r=1 ∧ η=2)) : Nonempty (DoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
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
  let G := DoubleFamily.two _ _ (fun he => hdiff (congrArg Prod.snd he)) hp hq
    (by change 0 < 4/(η+1+r); positivity) (by change 0 < 2/(η+1-r); positivity)
    ⟨0,Or.inl rfl⟩ ⟨0,Or.inl rfl⟩
  refine ⟨(doubleOpposite hr hr1 hmid).sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 0+p.1 1) he
  rw [doubleOpposite_sum] at hh
  fin_cases j <;> norm_num [G,DoubleFamily.two,doublePoint,cycle3] at hh

theorem doubleSlab_four {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) (hm2 : ¬(r=1 ∧ η= -2)) :
    Nonempty (DoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hnonneg (η : ℝ) (hη : 0 ≤ η) (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
      Nonempty (DoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
    by_cases hlo : η ≤ 1-r
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; apply h0; exact ⟨he,by linarith⟩)
      exact doubleSlab_four_low hr hrlt hη hlo
    · by_cases hhi : η < 3-r
      · exact doubleSlab_four_middle hr hr1 (by linarith) hhi
      · exact doubleSlab_four_high hr hr1 (by linarith) h2
  by_cases hη : 0 ≤ η
  · exact hnonneg η hη h0 h2
  obtain ⟨F⟩ := hnonneg (-η) (by linarith) (by rintro ⟨hr,he⟩; exact h0 ⟨hr,by linarith⟩)
    (by rintro ⟨hr,he⟩; exact hm2 ⟨hr,by linarith⟩)
  refine ⟨⟨fun i => slabFlip (F.point i),slabFlip.injective.comp F.inj,?_,F.positive,?_⟩⟩
  · intro i
    have he : slabFlip '' doubleSlab r (-η)=doubleSlab r η := by simpa using doubleSlab_flip r (-η)
    rw [← he,← image_extremePoints]; exact ⟨F.point i,F.extreme i,rfl⟩
  · intro i
    obtain ⟨j,hj | hj⟩ := F.saturated i
    · exact ⟨j,Or.inr (by change -(F.point i).1 j.castSucc= -1; rw [hj])⟩
    · exact ⟨j,Or.inl (by change -(F.point i).1 j.castSucc=1; rw [hj]; norm_num)⟩

end Kalai5.Cube3
