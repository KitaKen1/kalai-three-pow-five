import Kalai5.Cube3.TwoWidthConstruction
import Kalai5.Cube3.PolygonNormalFamilies

/-! Opposite supporting edges give actual endpoint pairs and two-level projections. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

lemma Config.signed_support_pair {j : Fin 4} {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k j) (balanceSign j • n)) :
    ∃ v w : Fin 8,C.c v=j ∧ C.c w=j ∧ C.signedPoint w ≠ C.signedPoint v ∧
      ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint w⟫ ∧
      ∀ z,C.c z=j → ⟪n,C.signedPoint z⟫≤⟪n,C.signedPoint v⟫ := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.1 hn.2
  obtain ⟨v,hv,hvp⟩ := Finset.mem_image.1 (mem_amax.1 hp).1
  obtain ⟨w,hw,hwq⟩ := Finset.mem_image.1 (mem_amax.1 hq).1
  have hvj : C.c v=j := by simpa using hv
  have hwj : C.c w=j := by simpa using hw
  have he (z : Fin 8) (hz : C.c z=j) :
      ⟪n,C.signedPoint z⟫=⟪balanceSign j • n,C.k z⟫ := by
    simp [Config.signedPoint,hz,real_inner_smul_left,real_inner_smul_right]
  refine ⟨v,w,hvj,hwj,?_,?_,?_⟩
  · intro hh
    have hvw := C.signedPoint_inj (hwj.trans hvj.symm) hh
    exact hpq (by rw [← hvp,← hwq,hvw])
  · rw [he v hvj,he w hwj,hvp,hwq]
    exact inner_eq_of_mem_amax hp hq
  · intro z hz
    rw [he z hz,he v hvj,hvp]
    exact (mem_amax.1 hp).2 _ (Finset.mem_image.2 ⟨z,by simp [hz],rfl⟩)

namespace ProjectionIntervals
variable {n m : E 2} (I : ProjectionIntervals C n)

lemma upper_pair_of_opposed {j : Fin 4}
    (hn : IsEdgeNormal (fibre C.c C.k j) m) (hm : IsEdgeNormal (fibre C.c C.k j) (-m))
    {a : ℝ} (ha : 0 < a) (he : n=a • m) :
    ∃ v w : Fin 8,C.c v=j ∧ C.c w=j ∧ C.signedPoint w ≠ C.signedPoint v ∧
      ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ ∧
      ⟪n,C.signedPoint w⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  have hs : IsEdgeNormal (fibre C.c C.k j) (balanceSign j • m) := by
    rcases balanceSign_sign j with hs | hs
    · simpa [hs] using hn
    · simpa [hs] using hm
  obtain ⟨v,w,hv,hw,hne,hvw,hmax⟩ := C.signed_support_pair hs
  have hscale (p : E 2) : ⟪n,p⟫=a*⟪m,p⟫ := by rw [he,real_inner_smul_left]
  have hbound := mul_le_mul_of_nonneg_left (hmax (I.hi j) (I.chi j)) ha.le
  have hvhi := I.upper v
  rw [hv,hscale,hscale] at hvhi
  have hvp : ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
    rw [hscale,hscale]; linarith
  refine ⟨v,w,hv,hw,hne,hvp,?_⟩
  rw [← hvp,hscale,hscale,hvw]

lemma lower_pair_of_opposed {j : Fin 4}
    (hn : IsEdgeNormal (fibre C.c C.k j) m) (hm : IsEdgeNormal (fibre C.c C.k j) (-m))
    {a : ℝ} (ha : 0 < a) (he : n=a • m) :
    ∃ v w : Fin 8,C.c v=j ∧ C.c w=j ∧ C.signedPoint w ≠ C.signedPoint v ∧
      ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∧
      ⟪n,C.signedPoint w⟫=⟪n,C.signedPoint (I.lo j)⟫ := by
  have hs : IsEdgeNormal (fibre C.c C.k j) (balanceSign j • (-m)) := by
    rcases balanceSign_sign j with hs | hs
    · simpa [hs] using hm
    · simpa [hs] using hn
  obtain ⟨v,w,hv,hw,hne,hvw,hmax⟩ := C.signed_support_pair hs
  have hscale (p : E 2) : ⟪n,p⟫=a*⟪m,p⟫ := by rw [he,real_inner_smul_left]
  have hbound := mul_le_mul_of_nonneg_left (hmax (I.lo j) (I.clo j)) ha.le
  simp only [inner_neg_left] at hbound hvw
  have hvlo := I.lower v
  rw [hv,hscale,hscale] at hvlo
  have hvp : ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ := by
    rw [hscale,hscale]; nlinarith
  refine ⟨v,w,hv,hw,hne,hvp,?_⟩
  rw [← hvp,hscale,hscale]
  congr 1
  linarith

lemma opposed_quad_two_levels {j : Fin 4} (h4 : (C.cls j).card=4)
    (hn : IsEdgeNormal (fibre C.c C.k j) m) (hm : IsEdgeNormal (fibre C.c C.k j) (-m))
    {a : ℝ} (he : n=a • m) (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∨
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  classical
  let A := fibre C.c C.k j
  have hdisj := amax_disjoint_neg (C.dim_fibre_eq_two (show 3 ≤ (C.cls j).card by omega)) hn.ne_zero
  have hunion : amax A m ∪ amax A (-m)=A := by
    apply Finset.eq_of_subset_of_card_le
      (Finset.union_subset (amax_subset _ _) (amax_subset _ _))
    rw [Finset.card_union_of_disjoint hdisj]
    have hcard : A.card=4 := (C.card_fibre j).trans h4
    have hp := hn.2
    have hq := hm.2
    omega
  obtain ⟨p,hp⟩ := Finset.card_pos.1 (show 0 < (amax A m).card from lt_trans Nat.zero_lt_one hn.2)
  obtain ⟨q,hq⟩ := Finset.card_pos.1 (show 0 < (amax A (-m)).card from lt_trans Nat.zero_lt_one hm.2)
  apply I.two_levels_of_values (β := a*balanceSign j*⟪m,p⟫) (γ := a*balanceSign j*⟪m,q⟫) _ v hv
  intro w hw
  have hmem : C.k w ∈ A := Finset.mem_image.2 ⟨w,by simp [hw],rfl⟩
  rw [← hunion,Finset.mem_union] at hmem
  have heval : ⟪n,C.signedPoint w⟫=a*balanceSign j*⟪m,C.k w⟫ := by
    rw [he,Config.signedPoint,hw,real_inner_smul_left,real_inner_smul_right]; ring
  rcases hmem with hmem | hmem
  · exact Or.inl (by rw [heval,inner_eq_of_mem_amax hmem hp])
  · have hh := inner_eq_of_mem_amax hmem hq
    simp only [inner_neg_left] at hh
    exact Or.inr (by rw [heval,show ⟪m,C.k w⟫=⟪m,q⟫ by linarith])

end ProjectionIntervals
end Kalai5.Cube3
