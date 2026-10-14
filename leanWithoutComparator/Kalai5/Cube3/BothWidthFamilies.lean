import Kalai5.Cube3.DoubleSlabCount

/-! Retain saturation of both positive-width intervals in a selected vertex family. -/
namespace Kalai5.Cube3
open Set

def BothWidthSaturated (r η : ℝ) (p : SlabPoint) : Prop :=
  |p.1 2|+r*p.2=1 ∧ |η*p.2-∑ i,p.1 i|+p.2=1

lemma BothWidthSaturated.swap {r η : ℝ} {p : SlabPoint} (h : BothWidthSaturated r η p) :
    BothWidthSaturated r η (doubleSwap p) := by
  refine ⟨h.1,?_⟩
  change |η*p.2-∑ i,(doubleSwap p).1 i|+p.2=1
  have he : ∑ i,(doubleSwap p).1 i=∑ i,p.1 i := by
    simp [doubleSwap,Fin.sum_univ_three]; ring
  rw [he]; exact h.2

lemma BothWidthSaturated.flip {r η : ℝ} {p : SlabPoint} (h : BothWidthSaturated r η p) :
    BothWidthSaturated r (-η) (slabFlip p) := by
  constructor
  · change |-(p.1 2)|+r*p.2=1
    rw [abs_neg]; exact h.1
  · change |(-η)*p.2-∑ i,(-p.1) i|+p.2=1
    simp only [PiLp.neg_apply,Finset.sum_neg_distrib]
    rw [show (-η)*p.2-(-(∑ i,p.1 i))= -(η*p.2-∑ i,p.1 i) by ring,abs_neg]
    exact h.2

structure BothDoubleFamily (r η : ℝ) (ι : Type*) extends DoubleFamily r η ι where
  both : ∀ i,BothWidthSaturated r η (point i)

namespace BothDoubleFamily

noncomputable def sum {r η : ℝ} {ι κ : Type*} (F : BothDoubleFamily r η ι)
    (G : BothDoubleFamily r η κ) (hd : ∀ i j,F.point i ≠ G.point j) :
    BothDoubleFamily r η (ι ⊕ κ) where
  toDoubleFamily := F.toDoubleFamily.sum G.toDoubleFamily hd
  both := by rintro (i | i); exact F.both i; exact G.both i

noncomputable def two {r η : ℝ} (p q : SlabPoint) (hne : p ≠ q)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hq : q ∈ (doubleSlab r η).extremePoints ℝ)
    (hpt : 0 < p.2) (hqt : 0 < q.2)
    (hps : ∃ j : Fin 2,p.1 j.castSucc=1 ∨ p.1 j.castSucc= -1)
    (hqs : ∃ j : Fin 2,q.1 j.castSucc=1 ∨ q.1 j.castSucc= -1)
    (hbp : BothWidthSaturated r η p) (hbq : BothWidthSaturated r η q) :
    BothDoubleFamily r η (Fin 2) where
  toDoubleFamily := DoubleFamily.two p q hne hp hq hpt hqt hps hqs
  both := by intro i; fin_cases i; exact hbp; exact hbq

noncomputable def swapped {r η : ℝ} (p : SlabPoint)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hb : BothWidthSaturated r η p) : BothDoubleFamily r η (Fin 2) where
  toDoubleFamily := DoubleFamily.swapped p hp hpt hs hne
  both := by intro i; fin_cases i; exact hb; exact hb.swap

lemma swapped_height {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hb : BothWidthSaturated r η p) (i : Fin 2) :
    ((swapped p hp hpt hs hne hb).point i).2=p.2 := by fin_cases i <;> rfl

lemma swapped_third {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (hpt : 0 < p.2)
    (hs : p.1 0=1 ∨ p.1 0= -1) (hne : p.1 0 ≠ p.1 1)
    (hb : BothWidthSaturated r η p) (i : Fin 2) :
    ((swapped p hp hpt hs hne hb).point i).1 2=p.1 2 := by fin_cases i <;> rfl

end BothDoubleFamily

lemma doubleSlab_cap_both {r η s v w : ℝ} (hr1 : r ≤ 1)
    (hw : w=1-r ∨ w=r-1) (he : η=s+v+w) :
    BothWidthSaturated r η (doublePoint s v w 1) := by
  constructor
  · change |w|+r*1=1
    rcases hw with rfl | rfl
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith)]; ring
  · change |η*1-∑ i,cycle3 s v w 0 i|+1=1
    rw [cycle3_sum,he]; norm_num

lemma doubleSlab_corner_both {r η s v σ t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hσ : σ=1 ∨ σ= -1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he : (η+σ*r+1)*t=s+v+σ+1) :
    BothWidthSaturated r η (doublePoint s v (σ*(1-r*t)) t) := by
  have hw : 0 ≤ 1-r*t := by nlinarith
  have hl : η*t-(s+v+σ*(1-r*t))=1-t := by nlinarith [he]
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  constructor
  · change |σ*(1-r*t)|+r*t=1
    rw [abs_mul,hσabs,one_mul,abs_of_nonneg hw]; ring
  · change |η*t-∑ i,cycle3 s v (σ*(1-r*t)) 0 i|+t=1
    rw [cycle3_sum,hl,abs_of_nonneg (by linarith)]; ring

end Kalai5.Cube3
