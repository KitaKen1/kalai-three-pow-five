import Kalai5.Cube3.TriangleSliceVertices

/-! Retain either of two specified saturated sides when counting a normal slice. -/

namespace Kalai5.Cube3
open Set

structure MarkedDoubleFamily (r η σ τ : ℝ) (ι : Type*) extends DoubleFamily r η ι where
  marked : ∀ i,widthForm r σ (point i)=1 ∨ slabForm η τ (point i)=1

lemma widthForm_flip (r σ : ℝ) (p : SlabPoint) :
    widthForm r (-σ) (slabFlip p)=widthForm r σ p := by
  change (-σ)*(-p.1 2)+r*p.2=σ*p.1 2+r*p.2; ring

lemma slabForm_flip (η τ : ℝ) (p : SlabPoint) :
    slabForm (-η) (-τ) (slabFlip p)=slabForm η τ p := by
  change (-τ)*((-η)*p.2-∑ i,(-p.1) i)+p.2=τ*(η*p.2-∑ i,p.1 i)+p.2
  simp only [PiLp.neg_apply,Finset.sum_neg_distrib]; ring

namespace MarkedDoubleFamily

noncomputable def sum {r η σ τ : ℝ} {ι κ : Type*} (F : MarkedDoubleFamily r η σ τ ι)
    (G : MarkedDoubleFamily r η σ τ κ) (hd : ∀ i j,F.point i ≠ G.point j) :
    MarkedDoubleFamily r η σ τ (ι ⊕ κ) where
  toDoubleFamily := F.toDoubleFamily.sum G.toDoubleFamily hd
  marked := by rintro (i | i); exact F.marked i; exact G.marked i

noncomputable def one {r η σ τ : ℝ} (p : SlabPoint)
    (hp : p ∈ (doubleSlab r η).extremePoints ℝ) (ht : 0 < p.2)
    (hs : ∃ i : Fin 2,p.1 i.castSucc=1 ∨ p.1 i.castSucc= -1)
    (hm : widthForm r σ p=1 ∨ slabForm η τ p=1) : MarkedDoubleFamily r η σ τ Unit where
  point _ := p
  inj _ _ _ := Subsingleton.elim _ _
  extreme _ := hp
  positive _ := ht
  saturated _ := hs
  marked _ := hm

noncomputable def reindex {r η σ τ : ℝ} {ι κ : Type*} (F : MarkedDoubleFamily r η σ τ ι)
    (e : κ → ι) (he : Function.Injective e) : MarkedDoubleFamily r η σ τ κ where
  point i := F.point (e i)
  inj := F.inj.comp he
  extreme i := F.extreme (e i)
  positive i := F.positive (e i)
  saturated i := F.saturated (e i)
  marked i := F.marked (e i)

noncomputable def flipped {r η σ τ : ℝ} {ι : Type*} (F : MarkedDoubleFamily r η σ τ ι) :
    MarkedDoubleFamily r (-η) (-σ) (-τ) ι where
  point i := slabFlip (F.point i)
  inj := slabFlip.injective.comp F.inj
  extreme := by
    intro i
    rw [← doubleSlab_flip r η,← image_extremePoints]
    exact ⟨F.point i,F.extreme i,rfl⟩
  positive := F.positive
  saturated := by
    intro i
    obtain ⟨j,hj | hj⟩ := F.saturated i
    · exact ⟨j,Or.inr (by change -(F.point i).1 j.castSucc= -1; rw [hj])⟩
    · exact ⟨j,Or.inl (by change -(F.point i).1 j.castSucc=1; rw [hj]; norm_num)⟩
  marked := by
    intro i
    rw [widthForm_flip,slabForm_flip]
    exact F.marked i

end MarkedDoubleFamily

noncomputable def UpperDoubleFamily.marked {r η : ℝ} {ι : Type*} (F : UpperDoubleFamily r η ι)
    (σ : ℝ) : MarkedDoubleFamily r η σ 1 ι where
  toDoubleFamily := F.toDoubleFamily
  marked i := Or.inr (F.upper i)

def selectThree : Fin 2 ⊕ Unit → Fin 2 ⊕ Fin 2 := Sum.elim Sum.inl (fun _ => Sum.inr 0)

lemma selectThree_injective : Function.Injective selectThree := by
  rintro (i | i) (j | j) he
  · exact congrArg Sum.inl (Sum.inl.inj he)
  · cases he
  · cases he
  · exact congrArg Sum.inr (Subsingleton.elim _ _)

lemma doubleSlab_cap_lower {r η : ℝ} {p : SlabPoint}
    (hp : p ∈ doubleSlab r η) (ht : p.2=1) : slabForm η (-1) p=1 := by
  have hh := hp.2.2.2
  rw [ht] at hh
  norm_num at hh
  change (-1)*(η*p.2-∑ i,p.1 i)+p.2=1
  rw [ht]; linarith

lemma doubleOpposite_width {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hη : 1-r < η) (i : Fin 2) :
    widthForm r 1 ((doubleOpposite hr hr1 hη).point i)=1 := by
  fin_cases i <;> change 1*(1*(1-r*(2/(η+1+r))))+r*(2/(η+1+r))=1 <;> ring

noncomputable def MarkedDoubleFamily.opposite {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : 1-r < η) : MarkedDoubleFamily r η 1 (-1) (Fin 2) where
  toDoubleFamily := doubleOpposite hr hr1 hη
  marked i := Or.inl (doubleOpposite_width hr hr1 hη i)

end Kalai5.Cube3
