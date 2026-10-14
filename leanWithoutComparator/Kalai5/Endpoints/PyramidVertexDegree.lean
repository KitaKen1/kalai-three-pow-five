import Kalai5.Endpoints.Weight8Basic

/-!
# Vertex degrees in a square pyramid

The apex belongs to all four triangular faces.  Its degree is at least four,
whereas every other vertex has degree at least three.  The total degree is 16,
so the apex has degree four and every base vertex has degree three.  This is
the local ingredient for the parity obstruction to two tetrahedra and six
square pyramids in an eight-vertex facet.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.four_le_vdeg_pyramid_apex {Y Q v : Set E5}
    (hY : Y ∈ faces P) (hY3 : dim Y = 3) (hy : tri3 P Y = (5, 8, 5))
    (hQ : Q ∈ faces P) (hQY : Q ⊆ Y) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hv : v ∈ faces P) (hvY : v ⊆ Y) (hv0 : dim v = 0) (hvQ : ¬ v ⊆ Q) :
    4 ≤ vdeg P Y v := by
  have hyc := hy
  simp only [tri3, Prod.mk.injEq] at hyc
  have hvmem : v ∈ vset P Y := ⟨hv, hvY, hv0⟩
  have hvnot : v ∉ vset P Q := fun h => hvQ h.2.1
  have hins : insert v (vset P Q) ⊆ vset P Y := by
    rintro w (hw | hw)
    · simpa [hw] using hvmem
    · exact ⟨hw.1, hw.2.1.trans hQY, hw.2.2⟩
  have hc : (insert v (vset P Q)).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem hvnot (hP.vset_finite Q), ← cnt_eq_vset, hQ4]
  have heq := Set.eq_of_subset_of_ncard_le hins
    (by rw [hc, ← cnt_eq_vset]; omega) (hP.vset_finite Y)
  have hother : ∀ T, T ∈ faces P → T ⊆ Y → dim T = 2 → T ≠ Q → v ⊆ T := by
    intro T hT hTY hT2 hTQ
    by_contra hnot
    have hsub : vset P T ⊆ vset P Q := by
      intro w hw
      have hm : w ∈ insert v (vset P Q) := by
        rw [heq]; exact ⟨hw.1, hw.2.1.trans hTY, hw.2.2⟩
      rcases hm with hm | hm
      · exact False.elim (hnot (hm ▸ hw.2.1))
      · exact hm
    exact hTQ (hP.eq_of_subset_of_dim_le hT hQ (hP.subset_of_vset hT hQ hsub) (by omega))
  have hsub : {T | T ∈ faces P ∧ T ⊆ Y ∧ dim T = 2} \ {Q} ⊆
      {T | T ∈ faces P ∧ v ⊆ T ∧ T ⊆ Y ∧ dim T = 2} := by
    rintro T ⟨⟨hT, hTY, hT2⟩, hne⟩
    exact ⟨hT, hother T hT hTY hT2 (by simpa using hne), hTY, hT2⟩
  have hcQ : Q ∈ {T | T ∈ faces P ∧ T ⊆ Y ∧ dim T = 2} := ⟨hQ, hQY, hQ2⟩
  have hle := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T hT => hT.1)
  rw [Set.ncard_sdiff_singleton_of_mem hcQ] at hle
  change cnt P Y 2 - 1 ≤ _ at hle
  have hd := (hP.vertex_in_threeface hY hY3 hv hvY hv0).1
  change vdeg P Y v = _ at hd
  rw [← hd] at hle
  omega

/-- The degrees in a square pyramid are three on its base and four at its apex. -/
theorem IsCSPolytope5.vdeg_square_pyramid {Y Q v : Set E5}
    (hY : Y ∈ faces P) (hY3 : dim Y = 3) (hy : tri3 P Y = (5, 8, 5))
    (hQ : Q ∈ faces P) (hQY : Q ⊆ Y) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hv : v ∈ faces P) (hvY : v ⊆ Y) (hv0 : dim v = 0) :
    vdeg P Y v = if v ⊆ Q then 3 else 4 := by
  have hyc := hy
  simp only [tri3, Prod.mk.injEq] at hyc
  set S := (hP.below_finite Y 0).toFinset with hS
  have hm : v ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact ⟨hv, hvY, hv0⟩
  have hcS : S.card = 5 := by
    rw [hS, ← Set.ncard_eq_toFinset_card _ (hP.below_finite Y 0)]
    change cnt P Y 0 = 5
    exact hyc.1
  have hfilt : S.filter (fun w => w ⊆ Q) = (hP.below_finite Q 0).toFinset := by
    ext w
    simp only [hS, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hw, -, hw0⟩, hwQ⟩; exact ⟨hw, hwQ, hw0⟩
    · rintro ⟨hw, hwQ, hw0⟩; exact ⟨⟨hw, hwQ.trans hQY, hw0⟩, hwQ⟩
  have hcQ : (S.filter (fun w => w ⊆ Q)).card = 4 := by
    rw [hfilt, ← Set.ncard_eq_toFinset_card _ (hP.below_finite Q 0)]
    exact hQ4
  have hsdeg : ∑ w ∈ S, (vdeg P Y w : ℤ) = 16 := by
    have hi := hP.incid_eq_sum_first Y 0 1
    rw [hP.incid_zero_one, hyc.2.1] at hi
    change 2 * 8 = ∑ w ∈ S, vdeg P Y w at hi
    exact_mod_cast hi.symm
  have hstarget : ∑ w ∈ S, (if w ⊆ Q then (3 : ℤ) else 4) = 16 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun w => w ⊆ Q)
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    rw [hcQ, hcS] at hsplit
    rw [hcQ]
    omega
  have hnonneg : ∀ w ∈ S,
      0 ≤ (vdeg P Y w : ℤ) - (if w ⊆ Q then (3 : ℤ) else 4) := by
    intro w hw
    rw [hS, Set.Finite.mem_toFinset] at hw
    by_cases hwQ : w ⊆ Q
    · rw [if_pos hwQ]
      have := (hP.vertex_in_threeface hY hY3 hw.1 hw.2.1 hw.2.2).2
      change 3 ≤ vdeg P Y w at this
      omega
    · rw [if_neg hwQ]
      have := hP.four_le_vdeg_pyramid_apex hY hY3 hy hQ hQY hQ2 hQ4 hw.1 hw.2.1 hw.2.2 hwQ
      omega
  have hz : ∑ w ∈ S, ((vdeg P Y w : ℤ) - (if w ⊆ Q then (3 : ℤ) else 4)) = 0 := by
    rw [Finset.sum_sub_distrib, hsdeg, hstarget]
    norm_num
  have hvz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hz v hm
  by_cases hvQ : v ⊆ Q <;> simp only [hvQ, ite_true, ite_false] at hvz ⊢ <;> omega

end Kalai5
