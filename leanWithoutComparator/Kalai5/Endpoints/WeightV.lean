import Kalai5.Endpoints.WeightB

/-!
# A catalogue-free Q55 weight eight for V = (8,19,19,8;39)

Quadrilaterals contained in a 3-face with other than five vertices cannot be
(5,5)-quadrilaterals. Thus a triangular prism gives `b55 + 3 ≤ q4`.
A seven-vertex 3-face gives `b55 = 0`. These two shortcuts, together with the
twelve type counts, improve the earlier weight four without classifying V.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The quadrilaterals of a non-five-vertex ridge are disjoint from b55. -/
lemma IsCSPolytope5.b55_add_q4_le {F T : Set E5}
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT5 : cnt P T 0 ≠ 5) :
    (b55set P F).ncard + q4 P T ≤ q4 P F := by
  let S : Set (Set E5) := {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}
  have hBfin : (b55set P F).Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hSfin : S.Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hd : Disjoint (b55set P F) S := by
    rw [Set.disjoint_left]
    intro Q hQB hQS
    have ht := hP.b55_pyr Q hQB T hT hQS.2.1 hTF hT3
    simp only [tri3, Prod.mk.injEq] at ht
    exact hT5 ht.1
  have hsub : b55set P F ∪ S ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    rintro Q (hQ | hQ)
    · exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1⟩
    · exact ⟨hQ.1, hQ.2.1.trans hTF, hQ.2.2.1, hQ.2.2.2⟩
  have hc := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun Q hQ => hQ.1)
  rw [Set.ncard_union_eq hd hBfin hSfin] at hc
  exact hc

/-- A triangular prism reserves three quadrilaterals outside b55. -/
lemma IsCSPolytope5.b55_add_three_le_of_prism {F : Set E5}
    (ht : 1 ≤ tcnt P F (6, 9, 5)) : (b55set P F).ncard + 3 ≤ q4 P F := by
  obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt ht
  have htc := ht
  simp only [tri3, Prod.mk.injEq] at htc
  have hl := hP.b55_add_q4_le hT hTF hT3 (by omega)
  rwa [(hP.q4_695 hT hT3 ht).1] at hl

/-- Two distinct non-five-vertex ridges share at most one quadrilateral,
so all but one of their combined quadrilateral counts are reserved outside b55. -/
lemma IsCSPolytope5.b55_add_q4_pair_le {F T U : Set E5}
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT5 : cnt P T 0 ≠ 5)
    (hU : U ∈ faces P) (hUF : U ⊆ F) (hU3 : dim U = 3) (hU5 : cnt P U 0 ≠ 5)
    (hTU : T ≠ U) : (b55set P F).ncard + q4 P T + q4 P U ≤ q4 P F + 1 := by
  let S : Set (Set E5) := {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}
  let R : Set (Set E5) := {Q | Q ∈ faces P ∧ Q ⊆ U ∧ dim Q = 2 ∧ cnt P Q 0 = 4}
  have hBfin : (b55set P F).Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hSfin : S.Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hRfin : R.Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hd : Disjoint (b55set P F) (S ∪ R) := by
    rw [Set.disjoint_left]
    rintro Q hQB (hQS | hQR)
    · have ht := hP.b55_pyr Q hQB T hT hQS.2.1 hTF hT3
      simp only [tri3, Prod.mk.injEq] at ht
      exact hT5 ht.1
    · have ht := hP.b55_pyr Q hQB U hU hQR.2.1 hUF hU3
      simp only [tri3, Prod.mk.injEq] at ht
      exact hU5 ht.1
  have hsub : b55set P F ∪ (S ∪ R) ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    rintro Q (hQ | hQ | hQ)
    · exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1⟩
    · exact ⟨hQ.1, hQ.2.1.trans hTF, hQ.2.2.1, hQ.2.2.2⟩
    · exact ⟨hQ.1, hQ.2.1.trans hUF, hQ.2.2.1, hQ.2.2.2⟩
  have hc := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun Q hQ => hQ.1)
  rw [Set.ncard_union_eq hd hBfin (hSfin.union hRfin)] at hc
  have hi : (S ∩ R).ncard ≤ 1 := by
    apply (Set.ncard_le_one (hSfin.inter_of_left R)).2
    intro Q hQ Q' hQ'
    have h1 := hP.inter_three_eq hQ.1.1 hQ.1.2.2.1 hT hT3 hU hU3 hTU hQ.1.2.1 hQ.2.2.1
    have h2 := hP.inter_three_eq hQ'.1.1 hQ'.1.2.2.1 hT hT3 hU hU3 hTU hQ'.1.2.1 hQ'.2.2.1
    exact h1.symm.trans h2
  have he := Set.ncard_union_add_ncard_inter S R hSfin hRfin
  change (b55set P F).ncard + (S ∪ R).ncard ≤ q4 P F at hc
  change (b55set P F).ncard + S.ncard + R.ncard ≤ q4 P F + 1
  omega

lemma IsCSPolytope5.b55_add_five_le_of_two_prisms {F : Set E5}
    (ht : 2 ≤ tcnt P F (6, 9, 5)) : (b55set P F).ncard + 5 ≤ q4 P F := by
  obtain ⟨T, U, hTU, hT, hU⟩ := hP.exists_two_of_tcnt ht
  have ht := hT.2.2.2
  have hu := hU.2.2.2
  simp only [tri3, Prod.mk.injEq] at ht hu
  have hl := hP.b55_add_q4_pair_le hT.1 hT.2.1 hT.2.2.1 (by omega)
    hU.1 hU.2.1 hU.2.2.1 (by omega) hTU
  rw [(hP.q4_695 hT.1 hT.2.2.1 hT.2.2.2).1,
    (hP.q4_695 hU.1 hU.2.2.1 hU.2.2.2).1] at hl
  omega

/-- Negative Q55 weight excludes every seven-vertex 3-face. -/
lemma IsCSPolytope5.tcnt_seven_eq_zero_of_q55_neg {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (hneg : q55w P F < 0) (e p : ℕ) : tcnt P F (7, e, p) = 0 := by
  by_contra hne
  obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7, e, p))
  simp only [tri3, Prod.mk.injEq] at ht
  have hb := (hP.facet_T7 hF h4 hn hT hTF hT3 ht.1).1
  have hw := hP.q55w_eq_b55 F
  omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.q55_v_eight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 39⟩) :
    8 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  have hb := hP.two_b55_le hF h4
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero, add_zero] at hl
  by_contra hbad
  have hneg : q55w P F < 0 := by omega
  have h7a := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 11 6
  have h7b := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 12 7
  have h7c := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 13 8
  have h7d := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 14 9
  have h7e := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 15 10
  have hprism : tcnt P F (6, 9, 5) = 0 := by
    by_contra hp0
    have := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6, 9, 5))
    omega
  omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.q55_19_40_ten {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 40⟩) :
    10 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  have hb := hP.two_b55_le hF h4
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero, add_zero] at hl
  by_contra hbad
  have hneg : q55w P F < 0 := by omega
  have h7a := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 11 6
  have h7b := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 12 7
  have h7c := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 13 8
  have h7d := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 14 9
  have h7e := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 15 10
  have hprism : tcnt P F (6, 9, 5) ≤ 1 := by
    by_contra hp0
    have := hP.b55_add_five_le_of_two_prisms (by omega : 2 ≤ tcnt P F (6, 9, 5))
    omega
  omega

set_option maxHeartbeats 2000000 in
/-- The nine-ridge row needs no eight-vertex classification: its only possible
nonsimplicial profiles have either one seven-vertex ridge or one prism. -/
theorem IsCSPolytope5.q55_19_20_9_eight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 20, 9, 41⟩) :
    8 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, c4⟩ := hP.facet8_arith hF h4 hn
  obtain ⟨l1, l2, l3⟩ := hP.facet8_local hF h4
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  have hcases : (tcnt P F (5, 8, 5) = 2 ∧ 1 ≤ tcnt P F (7, 11, 6)) ∨
      1 ≤ tcnt P F (6, 9, 5) := by omega
  rcases hcases with ⟨hpyr, h7⟩ | hprism
  · obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt h7
    simp only [tri3, Prod.mk.injEq] at ht
    obtain ⟨hb0, hpyrq⟩ := hP.facet_T7 hF h4 hn hT hTF hT3 ht.1
    have hmono := hP.b55_add_q4_le hT hTF hT3 (by omega)
    omega
  · have hb3 := hP.b55_add_three_le_of_prism hprism
    omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.q55_19_41_twelve {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 41⟩) :
    12 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  have hb := hP.two_b55_le hF h4
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero, add_zero] at hl
  by_contra hbad
  have hneg : q55w P F < 0 := by omega
  have h7a := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 11 6
  have h7b := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 12 7
  have h7c := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 13 8
  have h7d := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 14 9
  have h7e := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn hneg 15 10
  omega

end Kalai5
