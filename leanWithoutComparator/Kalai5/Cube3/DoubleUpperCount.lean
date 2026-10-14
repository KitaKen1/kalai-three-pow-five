import Kalai5.Cube3.TwoWidthExceptional

/-! Four positive slice vertices on the upper side of the wider interval, for nonnegative drift. -/

namespace Kalai5.Cube3
open Set

lemma slabForm_doublePoint (η s v w t : ℝ) :
    slabForm η 1 (doublePoint s v w t)=η*t-(s+v+w)+t := by
  change 1*(η*t-∑ i,cycle3 s v w 0 i)+t=_
  rw [cycle3_sum]; ring

lemma doubleSlab_cap_upper {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ doubleSlab r η) (ht : p.2=1) : slabForm η 1 p=1 := by
  have hh := hp.2.2.2
  rw [ht] at hh
  norm_num at hh
  change 1*(η*p.2-∑ i,p.1 i)+p.2=1
  rw [ht]; linarith

lemma doubleSlab_corner_upper {r η s v σ t : ℝ}
    (he : (η+σ*r+1)*t=s+v+σ+1) :
    slabForm η 1 (doublePoint s v (σ*(1-r*t)) t)=1 := by
  rw [slabForm_doublePoint]; nlinarith [he]

lemma DoubleFamily.swapped_form {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1) (i : Fin 2) :
    slabForm η 1 ((DoubleFamily.swapped p hp hpt hs hne).point i)=slabForm η 1 p := by
  fin_cases i
  · rfl
  · simp [DoubleFamily.swapped,DoubleFamily.two,doubleSwap,slabForm,Fin.sum_univ_three]
    ring

structure UpperDoubleFamily (r η : ℝ) (ι : Type*) extends DoubleFamily r η ι where
  upper : ∀ i,slabForm η 1 (point i)=1

namespace UpperDoubleFamily

noncomputable def sum {r η : ℝ} {ι κ : Type*} (F : UpperDoubleFamily r η ι)
    (G : UpperDoubleFamily r η κ) (hd : ∀ i j,F.point i ≠ G.point j) :
    UpperDoubleFamily r η (ι ⊕ κ) where
  toDoubleFamily := F.toDoubleFamily.sum G.toDoubleFamily hd
  upper := by rintro (i | i); exact F.upper i; exact G.upper i

noncomputable def swapped {r η : ℝ} (p : SlabPoint)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hu : slabForm η 1 p=1) : UpperDoubleFamily r η (Fin 2) where
  toDoubleFamily := DoubleFamily.swapped p hp hpt hs hne
  upper i := (DoubleFamily.swapped_form hp hpt hs hne i).trans hu

lemma swapped_third {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hu : slabForm η 1 p=1) (i : Fin 2) :
    ((swapped p hp hpt hs hne hu).point i).1 2=p.1 2 := by fin_cases i <;> rfl

lemma swapped_height {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hu : slabForm η 1 p=1) (i : Fin 2) :
    ((swapped p hp hpt hs hne hu).point i).2=p.2 := by fin_cases i <;> rfl

noncomputable def opposite {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) :
    UpperDoubleFamily r η (Fin 2) where
  toDoubleFamily := doubleOpposite hr hr1 hη
  upper := by
    intro i
    have hd : η+1+r ≠ 0 := by linarith
    fin_cases i <;>
      simp [doubleOpposite,DoubleFamily.swapped,DoubleFamily.two,doubleSwap,slabForm,
        doublePoint,cycle3,Fin.sum_univ_three] <;> field_simp <;> ring

end UpperDoubleFamily

lemma doubleSlab_upper_four_low {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hη : 0 ≤ η) (hlo : η ≤ 1-r) : Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := -1) (v := η+r) (w := 1-r)
    (Or.inr rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let F := UpperDoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
    (by change 1 ≠ η-r; linarith) (doubleSlab_cap_upper hp.1 rfl)
  let G := UpperDoubleFamily.swapped _ hq (by norm_num [doublePoint]) (Or.inr rfl)
    (by change -1 ≠ η+r; linarith) (doubleSlab_cap_upper hq.1 rfl)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 2) he
  rw [UpperDoubleFamily.swapped_third,UpperDoubleFamily.swapped_third] at hh
  change r-1=1-r at hh; linarith

lemma doubleSlab_upper_four_middle {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hlo : 1-r < η) (hhi : η < 3-r) : Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1 (s := 1) (v := η+r-2) (w := 1-r)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let G := UpperDoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
    (by change 1 ≠ η+r-2; linarith) (doubleSlab_cap_upper hp.1 rfl)
  refine ⟨(UpperDoubleFamily.opposite hr hr1 hlo).sum G ?_⟩
  intro i j he
  have hh := congrArg Prod.snd he
  change ((doubleOpposite hr hr1 hlo).point i).2=(G.point j).2 at hh
  rw [doubleOpposite_height,UpperDoubleFamily.swapped_height] at hh
  change 2/(η+1+r)=1 at hh
  have hlt : 2/(η+1+r)<1 := (div_lt_one (by linarith)).2 (by linarith)
  linarith

lemma doubleSlab_upper_four_high {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hhi : 3-r ≤ η) (hne : ¬(r=1 ∧ η=2)) : Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hplus : 0 < η+1+r := by linarith
  have hminus : 0 < η+1-r := by linarith
  have hmid : 1-r < η := by linarith
  have hdiff : 4/(η+1+r) ≠ 2/(η+1-r) := by
    intro hh
    have hh := (div_eq_div_iff hplus.ne' hminus.ne').1 hh
    apply hne
    constructor <;> linarith
  have hep : (η+1*r+1)*(4/(η+1+r))=1+1+1+1 := by field_simp; ring
  have heq : (η+(-1)*r+1)*(2/(η+1-r))=1+1+(-1)+1 := by field_simp; ring
  have hp := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := 1)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (by positivity : 0 < 4/(η+1+r))
    ((div_le_one hplus).2 (by linarith)) (by linarith) hep
  have hq := doubleSlab_corner_point hr.le hr1 (s := 1) (v := 1) (σ := -1)
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (by positivity : 0 < 2/(η+1-r))
    ((div_le_one hminus).2 (by linarith)) (by linarith) heq
  let G : UpperDoubleFamily r η (Fin 2) :=
    ⟨DoubleFamily.two _ _ (fun he => hdiff (congrArg Prod.snd he)) hp hq
      (by change 0 < 4/(η+1+r); positivity) (by change 0 < 2/(η+1-r); positivity)
      ⟨0,Or.inl rfl⟩ ⟨0,Or.inl rfl⟩,
      by intro i; fin_cases i; exact doubleSlab_corner_upper hep; exact doubleSlab_corner_upper heq⟩
  refine ⟨(UpperDoubleFamily.opposite hr hr1 hmid).sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 0+p.1 1) he
  change ((doubleOpposite hr hr1 hmid).point i).1 0+
    ((doubleOpposite hr hr1 hmid).point i).1 1=(G.point j).1 0+(G.point j).1 1 at hh
  rw [doubleOpposite_sum] at hh
  fin_cases j <;> norm_num [G,DoubleFamily.two,doublePoint,cycle3] at hh

theorem doubleSlab_upper_four {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 ≤ η)
    (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
    Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  by_cases hlo : η ≤ 1-r
  · have hrlt : r < 1 := lt_of_le_of_ne hr1 (by intro he; apply h0; exact ⟨he,by linarith⟩)
    exact doubleSlab_upper_four_low hr hrlt hη hlo
  · by_cases hhi : η < 3-r
    · exact doubleSlab_upper_four_middle hr hr1 (by linarith) hhi
    · exact doubleSlab_upper_four_high hr hr1 (by linarith) h2

end Kalai5.Cube3
