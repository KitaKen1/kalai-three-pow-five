import Kalai5.Cube3.DoubleSlabCount

/-! A cap vertex fixed by both zero-width coordinates, even when neither width side is tight. -/
namespace Kalai5.Cube3
open Set

lemma doubleSlab_cap_zero_pair {r η : ℝ} {z : SlabPoint}
    (hz : z ∈ doubleSlab r η) (ht : z.2=1)
    (h0 : z.1 0=1 ∨ z.1 0= -1) (h1 : z.1 1=1 ∨ z.1 1= -1) :
    z ∈ (doubleSlab r η).extremePoints ℝ := by
  refine ⟨hz,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hp0 := (endpoint_combination hp.1 hq.1 ha hb hab
    (by simpa using congrArg (fun p : SlabPoint => p.1 0) he) h0).1
  have hp1 := (endpoint_combination hp.2.1 hq.2.1 ha hb hab
    (by simpa using congrArg (fun p : SlabPoint => p.1 1) he) h1).1
  have hpt : p.2=1 := (endpoint_combination (doubleSlab_height_bound hp)
    (doubleSlab_height_bound hq) ha hb hab
    (by simpa [ht] using congrArg Prod.snd he) (Or.inl rfl)).1
  have hsum (w : SlabPoint) (hw : w ∈ doubleSlab r η) (hwt : w.2=1) : ∑ i,w.1 i=η := by
    have hh := hw.2.2.2
    rw [hwt] at hh
    norm_num at hh
    linarith
  have hsp := hsum p hp hpt
  have hsz := hsum z hz ht
  rw [Fin.sum_univ_three,hp0,hp1] at hsp
  rw [Fin.sum_univ_three] at hsz
  apply Prod.ext _ (hpt.trans ht.symm)
  ext i; fin_cases i
  · exact hp0
  · exact hp1
  · change p.1 2=z.1 2; linarith

lemma doubleSlab_zero_cap {r η : ℝ} (hη : |η|+r≤1) :
    doublePoint 1 (-1) η 1 ∈ (doubleSlab r η).extremePoints ℝ := by
  apply doubleSlab_cap_zero_pair (ht := rfl) (h0 := Or.inl rfl) (h1 := Or.inr rfl)
  refine ⟨by norm_num [doublePoint,cycle3],by norm_num [doublePoint,cycle3],?_,?_⟩
  · change |η|+r*|1|≤1; simpa using hη
  · change |η*1-∑ i,cycle3 1 (-1) η 0 i|+|1|≤1
    rw [cycle3_sum]; norm_num

end Kalai5.Cube3
