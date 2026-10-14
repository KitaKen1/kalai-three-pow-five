import Kalai5.Cube3.TripleCount

/-! Two zero-width coordinates and two shrinking coordinates on a normal line. -/

namespace Kalai5.Cube3

open Set

def doubleSlab (r η : ℝ) : Set SlabPoint :=
  {p | |p.1 0| ≤ 1 ∧ |p.1 1| ≤ 1 ∧ |p.1 2| + r*|p.2| ≤ 1 ∧
    |η*p.2 - ∑ i,p.1 i| + |p.2| ≤ 1}

noncomputable def widthForm (r σ : ℝ) : SlabPoint →ₗ[ℝ] ℝ where
  toFun p := σ*p.1 2 + r*p.2
  map_add' := by intro p q; simp only [Prod.fst_add,Prod.snd_add,PiLp.add_apply]; ring
  map_smul' := by
    intro t p
    simp only [Prod.smul_fst,Prod.smul_snd,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

lemma widthForm_bound {r η σ : ℝ} (hr : 0 ≤ r) (hσ : |σ| = 1)
    {p : SlabPoint} (hp : p ∈ doubleSlab r η) : |widthForm r σ p| ≤ 1 := by
  apply (abs_add_le _ _).trans
  simpa only [abs_mul,hσ,one_mul,abs_of_nonneg hr] using hp.2.2.1

lemma doubleSlab_form_bound {r η : ℝ} {p : SlabPoint} (hp : p ∈ doubleSlab r η) :
    |slabForm η 1 p| ≤ 1 := by
  apply (abs_add_le _ _).trans
  simpa using hp.2.2.2

lemma doubleSlab_height_bound {r η : ℝ} {p : SlabPoint} (hp : p ∈ doubleSlab r η) :
    |p.2| ≤ 1 := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hp.2.2.2

lemma widthForm_fixed {r η σ : ℝ} (hr : 0 ≤ r) (hσ : |σ| = 1)
    {p q z : SlabPoint} (hp : p ∈ doubleSlab r η) (hq : q ∈ doubleSlab r η)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (he : a • p + b • q = z) (hz : widthForm r σ z = 1) :
    widthForm r σ p = 1 := by
  apply (endpoint_combination (widthForm_bound hr hσ hp) (widthForm_bound hr hσ hq)
    ha hb hab _ (Or.inl rfl)).1
  have h := congrArg (widthForm r σ) he
  simpa only [map_add,map_smul,smul_eq_mul,hz] using h

lemma doubleSlab_cap {r η σ : ℝ} (hr : 0 ≤ r) (hσ : σ=1 ∨ σ= -1)
    {z : SlabPoint} (hz : z ∈ doubleSlab r η) (ht : z.2=1)
    (h0 : z.1 0=1 ∨ z.1 0= -1) (hw : widthForm r σ z=1) :
    z ∈ (doubleSlab r η).extremePoints ℝ := by
  refine ⟨hz,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hp0 := (endpoint_combination hp.1 hq.1 ha hb hab
    (by simpa using congrArg (fun p : SlabPoint => p.1 0) he) h0).1
  have hpt : p.2=1 := (endpoint_combination (doubleSlab_height_bound hp)
    (doubleSlab_height_bound hq) ha hb hab
    (by simpa [ht] using congrArg Prod.snd he) (Or.inl rfl)).1
  have hpw := widthForm_fixed hr hσabs hp hq ha hb hab he hw
  change σ*p.1 2 + r*p.2=1 at hpw
  change σ*z.1 2 + r*z.2=1 at hw
  have hp2 : p.1 2=z.1 2 := by
    rw [hpt] at hpw; rw [ht] at hw
    rcases hσ with rfl | rfl <;> linarith
  have hsum (w : SlabPoint) (hw : w ∈ doubleSlab r η) (hwt : w.2=1) :
      ∑ i,w.1 i=η := by
    have hh := hw.2.2.2
    rw [hwt] at hh
    norm_num at hh
    linarith
  have hsp := hsum p hp hpt
  have hsz := hsum z hz ht
  rw [Fin.sum_univ_three,hp0,hp2] at hsp
  rw [Fin.sum_univ_three] at hsz
  apply Prod.ext _ (hpt.trans ht.symm)
  ext i; fin_cases i
  · exact hp0
  · change p.1 1=z.1 1; linarith
  · exact hp2

lemma doubleSlab_corner {r η σ : ℝ} (hr : 0 ≤ r) (hσ : σ=1 ∨ σ= -1)
    {z : SlabPoint} (hz : z ∈ doubleSlab r η)
    (h0 : z.1 0=1 ∨ z.1 0= -1) (h1 : z.1 1=1 ∨ z.1 1= -1)
    (hw : widthForm r σ z=1) (hf : slabForm η 1 z=1)
    (hc : η+σ*r+1 ≠ 0) : z ∈ (doubleSlab r η).extremePoints ℝ := by
  refine ⟨hz,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hp0 := (endpoint_combination hp.1 hq.1 ha hb hab
    (by simpa using congrArg (fun p : SlabPoint => p.1 0) he) h0).1
  have hp1 := (endpoint_combination hp.2.1 hq.2.1 ha hb hab
    (by simpa using congrArg (fun p : SlabPoint => p.1 1) he) h1).1
  have hpw := widthForm_fixed hr hσabs hp hq ha hb hab he hw
  have hpf : slabForm η 1 p=1 := by
    apply (endpoint_combination (doubleSlab_form_bound hp) (doubleSlab_form_bound hq)
      ha hb hab _ (Or.inl rfl)).1
    have hh := congrArg (slabForm η 1) he
    simpa only [map_add,map_smul,smul_eq_mul,hf] using hh
  change σ*p.1 2+r*p.2=1 at hpw
  change σ*z.1 2+r*z.2=1 at hw
  change 1*(η*p.2-∑ i,p.1 i)+p.2=1 at hpf
  change 1*(η*z.2-∑ i,z.1 i)+z.2=1 at hf
  rw [Fin.sum_univ_three,hp0,hp1] at hpf
  rw [Fin.sum_univ_three] at hf
  have hpt : p.2=z.2 := by
    apply sub_eq_zero.1
    apply (mul_eq_zero.1 (show (η+σ*r+1)*(p.2-z.2)=0 from ?_)).resolve_left hc
    rcases hσ with rfl | rfl <;> nlinarith [hpw,hw,hpf,hf]
  have hp2 : p.1 2=z.1 2 := by rw [hpt] at hpf; linarith
  apply Prod.ext _ hpt
  ext i; fin_cases i <;> assumption

noncomputable def doubleSwap : SlabPoint ≃ₗ[ℝ] SlabPoint where
  toFun p := ((WithLp.equiv 2 (Fin 3 → ℝ)).symm ![p.1 1,p.1 0,p.1 2],p.2)
  invFun p := ((WithLp.equiv 2 (Fin 3 → ℝ)).symm ![p.1 1,p.1 0,p.1 2],p.2)
  left_inv p := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_add' p q := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_smul' t p := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl

lemma doubleSlab_swap (r η : ℝ) : doubleSwap '' doubleSlab r η = doubleSlab r η := by
  have hm (p : SlabPoint) (hp : p ∈ doubleSlab r η) : doubleSwap p ∈ doubleSlab r η := by
    refine ⟨hp.2.1,hp.1,hp.2.2.1,?_⟩
    have he : (∑ i,(doubleSwap p).1 i) = ∑ i,p.1 i := by
      simp [Fin.sum_univ_three,doubleSwap]; ring
    rw [he]; exact hp.2.2.2
  ext p; constructor
  · rintro ⟨q,hq,rfl⟩; exact hm q hq
  · intro hp; exact ⟨doubleSwap p,hm p hp,by
      apply Prod.ext
      · ext i; fin_cases i <;> rfl
      · rfl⟩

lemma doubleSlab_flip (r η : ℝ) : slabFlip '' doubleSlab r η = doubleSlab r (-η) := by
  have hm (η : ℝ) (p : SlabPoint) (hp : p ∈ doubleSlab r η) :
      slabFlip p ∈ doubleSlab r (-η) := by
    refine ⟨by simpa [slabFlip] using hp.1,by simpa [slabFlip] using hp.2.1,
      by simpa [slabFlip] using hp.2.2.1,?_⟩
    change |-η*p.2-∑ i,(-p.1) i|+|p.2|≤1
    have he : -η*p.2-∑ i,(-p.1) i = -(η*p.2-∑ i,p.1 i) := by
      simp [Finset.sum_neg_distrib]; ring
    rw [he,abs_neg]; exact hp.2.2.2
  ext p; constructor
  · rintro ⟨q,hq,rfl⟩; exact hm η q hq
  · intro hp
    refine ⟨slabFlip p,?_,by simp [slabFlip]⟩
    simpa using hm (-η) p hp

end Kalai5.Cube3
