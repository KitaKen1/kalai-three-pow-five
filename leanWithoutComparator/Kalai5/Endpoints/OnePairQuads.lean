import Kalai5.Endpoints.OnePairLocal

/-!
# Exactly two Y facets through every quadrilateral

The weaker quadrilateral-link budget is also saturated. Its summands over
quadrilaterals are nonpositive, so each is zero. A triangular upper link then
contains exactly two Y facets. This avoids constructing the link graph.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.fewFull18_one_pair_sum_weight
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    ∑ F ∈ (hP.kfaces_finite 4).toFinset,
      (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F = 0 := by
  obtain ⟨hall, hY, hJ, hH, -, -⟩ := hP.fewFull18_one_pair_profile hv hh hc hlt
  have hs := sum_three qlWeight hall (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hY, hJ, hH] at hs
  have hs72 : ((facetRows P).map qlWeight).sum = 72 := hs
  rw [hP.facetRows_sum] at hs72
  have hsZ : ∑ F ∈ (hP.kfaces_finite 4).toFinset,
      (qlWeight (faceRow P F) : ℤ) = 72 := by exact_mod_cast hs72
  have hd := hP.fewFull18_one_pair_flagData hv hh hc hlt
  have hexc := hP.sum_exc
  have hu := hP.sum_weight_le
  rw [hd] at hexc
  norm_num at hexc
  have hA : (flagDataOf P).A = 0 := by rw [hd]; norm_num [FlagData.A]
  rw [hA, mul_zero] at hu
  have hl := Finset.sum_le_sum (show ∀ F ∈ (hP.kfaces_finite 4).toFinset,
      (qlWeight (faceRow P F) : ℤ) ≤
      (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F + 2 * exc P F from by
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    exact hP.weight_ge hF.1 hF.2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsZ, hexc] at hl
  linarith only [hl, hu]

/-- Every quadrilateral in the residual one-pair configuration lies in
exactly two Y facets. Its third facet is J or H. -/
theorem IsCSPolytope5.fewFull18_one_pair_quad_two_Y
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    ((hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)).card = 2 := by
  have hG := (hP.fewFull18_one_pair_stresses hv hh hc hlt).1
  have hsum := hP.fewFull18_one_pair_sum_weight hv hh hc hlt
  have hexp : ∀ F, (if goodRow (faceRow P F) then (1 : ℤ) else -2) * q4 P F =
      ∑ R ∈ (hP.below_finite F 2).toFinset,
        if cnt P R 0 = 4 then (if goodRow (faceRow P F) then (1 : ℤ) else -2) else 0 := by
    intro F
    rw [hP.q4_eq_card, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl fun F _ => hexp F] at hsum
  rw [Finset.sum_comm' (t' := (hP.kfaces_finite 2).toFinset)
    (s' := fun R => (hP.above_finite R 4).toFinset)] at hsum
  swap
  · intro F R
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  let w : Set E5 → ℤ := fun R => ∑ F ∈ (hP.above_finite R 4).toFinset,
    if cnt P R 0 = 4 then (if goodRow (faceRow P F) then (1 : ℤ) else -2) else 0
  have hn : ∀ R ∈ (hP.kfaces_finite 2).toFinset, w R ≤ 0 := by
    intro R hR
    rw [Set.Finite.mem_toFinset] at hR
    by_cases hR4 : cnt P R 0 = 4
    · have hi := hP.quad_ineq hR.1 hR.2 hR4
      have hthree := hP.quad_up_eq_three_of_G_eq_zero hG hR.1 hR.2 hR4
      rw [Set.ncard_eq_toFinset_card _ (hP.above_finite R 4)] at hthree
      change (hP.above_finite R 4).toFinset.card = 3 at hthree
      simp only [w, hR4, ite_true]
      exact hi.trans (by rw [hthree]; norm_num)
    · simp [w, hR4]
  have heq : (∑ R ∈ (hP.kfaces_finite 2).toFinset, w R) =
      ∑ _R ∈ (hP.kfaces_finite 2).toFinset, (0 : ℤ) := by
    simpa only [Finset.sum_const_zero] using hsum
  have hzero := (Finset.sum_eq_sum_iff_of_le hn).1 heq Q
    (by rw [Set.Finite.mem_toFinset]; exact ⟨hQ, h2⟩)
  simp only [w, hQ4, ite_true] at hzero
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_one] at hzero
  have hthree := hP.quad_up_eq_three_of_G_eq_zero hG hQ h2 hQ4
  rw [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)] at hthree
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (hP.above_finite Q 4).toFinset) (fun F => goodRow (faceRow P F))
  have hgood : ((hP.above_finite Q 4).toFinset.filter
      (fun F => goodRow (faceRow P F))).card = 2 := by omega
  have hall := (hP.fewFull18_one_pair_profile hv hh hc hlt).1
  have hfilter : (hP.above_finite Q 4).toFinset.filter (fun F => goodRow (faceRow P F)) =
      (hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow) := by
    apply Finset.filter_congr
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    have hm : faceRow P F ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨F, Finset.mem_toList.2 (by
        rw [Set.Finite.mem_toFinset]; exact ⟨hF.1, hF.2.2⟩), rfl⟩
    rcases hall _ hm with h | h | h <;>
      norm_num [goodRow, h, excRow, eRow, OnePairProfile.jRow, OnePairProfile.fullRow]
  rwa [hfilter] at hgood

/-- Counting Y-quadrilateral incidences gives exactly twelve quadrilaterals. -/
theorem IsCSPolytope5.fewFull18_one_pair_twelve_quads
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    {Q | Q ∈ faces P ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.ncard = 12 := by
  let cost : Row → ℕ := fun R => if R = excRow then 3 else 0
  obtain ⟨hall, hY, hJ, hH, -, -⟩ := hP.fewFull18_one_pair_profile hv hh hc hlt
  have hs := sum_three cost hall (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hY, hJ, hH] at hs
  norm_num [cost, excRow, OnePairProfile.jRow, OnePairProfile.fullRow] at hs
  rw [hP.facetRows_sum] at hs
  have hsum : (∑ F ∈ (hP.kfaces_finite 4).toFinset,
      if faceRow P F = excRow then q4 P F else 0) = 24 := by
    calc _ = ∑ F ∈ (hP.kfaces_finite 4).toFinset, cost (faceRow P F) := by
          refine Finset.sum_congr rfl fun F hF => ?_
          rw [Set.Finite.mem_toFinset] at hF
          by_cases hY : faceRow P F = excRow
          · have hq := (hP.Y_quad hF.1 hF.2 hY).1
            simp only [hY, ite_true, cost]
            exact_mod_cast hq
          · simp only [cost, hY, ite_false]
      _ = 24 := hs
  have hexp : ∀ F, (if faceRow P F = excRow then q4 P F else 0) =
      ∑ Q ∈ (hP.below_finite F 2).toFinset,
        if cnt P Q 0 = 4 then (if faceRow P F = excRow then (1 : ℕ) else 0) else 0 := by
    intro F
    by_cases hY : faceRow P F = excRow
    · simp only [hY, ite_true, hP.q4_eq_card, Finset.card_filter]
    · simp [hY]
  rw [Finset.sum_congr rfl fun F _ => hexp F] at hsum
  rw [Finset.sum_comm' (t' := (hP.kfaces_finite 2).toFinset)
    (s' := fun Q => (hP.above_finite Q 4).toFinset)] at hsum
  swap
  · intro F Q
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  have hterm : ∀ Q ∈ (hP.kfaces_finite 2).toFinset,
      (∑ F ∈ (hP.above_finite Q 4).toFinset,
        if cnt P Q 0 = 4 then (if faceRow P F = excRow then (1 : ℕ) else 0) else 0) =
        if cnt P Q 0 = 4 then 2 else 0 := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    by_cases hQ4 : cnt P Q 0 = 4
    · simp only [hQ4, ite_true]
      rw [← Finset.card_filter]
      exact hP.fewFull18_one_pair_quad_two_Y hv hh hc hlt hQ.1 hQ.2 hQ4
    · simp [hQ4]
  rw [Finset.sum_congr rfl hterm] at hsum
  have hcard : 2 * ((hP.kfaces_finite 2).toFinset.filter fun Q => cnt P Q 0 = 4).card = 24 := by
    rw [Finset.card_filter, Finset.mul_sum]
    simpa only [mul_ite, mul_one, mul_zero] using hsum
  have hset : {Q | Q ∈ faces P ∧ dim Q = 2 ∧ cnt P Q 0 = 4} =
      ↑((hP.kfaces_finite 2).toFinset.filter fun Q => cnt P Q 0 = 4) := by
    ext Q
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  rw [hset, Set.ncard_coe_finset]
  omega

end Kalai5
