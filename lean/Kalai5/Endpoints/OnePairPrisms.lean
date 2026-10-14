import Kalai5.Endpoints.OnePairQuads

/-!
# The prism partners of the eight Y facets

A Y facet has a unique triangular prism. That prism contains all three of
its quadrilaterals. In the one-pair residual configuration the other facet
through the prism is again Y, and it is the only other Y through any of these
quadrilaterals. No vertex labelling or prism realization is needed.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The unique prism of Y contains every quadrilateral of Y. -/
theorem IsCSPolytope5.Y_prism_base {Y : Set E5}
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hrow : faceRow P Y = excRow) :
    ∃ K, K ∈ faces P ∧ K ⊆ Y ∧ dim K = 3 ∧ tri3 P K = (6, 9, 5) ∧
      (∀ T ∈ faces P, T ⊆ Y → dim T = 3 → tri3 P T = (6, 9, 5) → T = K) ∧
      (∀ Q ∈ faces P, Q ⊆ Y → dim Q = 2 → cnt P Q 0 = 4 → Q ⊆ K) := by
  have hn : cnt P Y 0 = 7 := congrArg Row.n hrow
  obtain ⟨hm, he⟩ := hP.facet_rowX hY hY4 hn.le
  have hp := smallRowsX_exc _ hm (by change rowOf Y = excRow; rw [he, hrow])
  obtain ⟨-, -, -, hc, -, -, -⟩ := hP.profile_counts hY hY4 hn.le hp
  obtain ⟨K, hKsingle⟩ := Finset.card_eq_one.1 hc
  obtain ⟨hK, ht⟩ := mem_of_filter_eq_singleton hKsingle
  rw [Set.Finite.mem_toFinset] at hK
  have hqK := (hP.q4_695 hK.1 hK.2.2 ht).1
  have hqY := (hP.Y_quad hY hY4 hrow).1
  have hsub : {Q | Q ∈ faces P ∧ Q ⊆ K ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ Y ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    intro Q hQ
    exact ⟨hQ.1, hQ.2.1.trans hK.2.1, hQ.2.2⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (show q4 P Y ≤ q4 P K by omega)
    (hP.faces_finite.subset fun Q hQ => hQ.1)
  refine ⟨K, hK.1, hK.2.1, hK.2.2, ht, ?_, ?_⟩
  · intro T hT hTY hT3 htT
    exact eq_of_filter_eq_singleton hKsingle
      (by rw [Set.Finite.mem_toFinset]; exact ⟨hT, hTY, hT3⟩) htT
  · intro Q hQ hQY hQ2 hQ4
    have hmem : Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ Y ∧ dim Q = 2 ∧ cnt P Q 0 = 4} :=
      ⟨hQ, hQY, hQ2, hQ4⟩
    rw [← heq] at hmem
    exact hmem.2.1

/-- J has only tetrahedra, square pyramids, and triangular bipyramids. -/
theorem IsCSPolytope5.J_three_types {J : Set E5}
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hrow : faceRow P J = OnePairProfile.jRow) :
    ∀ T ∈ faces P, T ⊆ J → dim T = 3 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (5, 9, 6) := by
  have hn : cnt P J 0 = 7 := congrArg Row.n hrow
  obtain ⟨hm, he⟩ := hP.facet_rowX hJ hJ4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 = OnePairProfile.jRow →
      X.2.1 = [3, 2, 2, 0, 0, 0, 0] := by decide +kernel
  have hp := hcheck _ hm (by change rowOf J = _; rw [he, hrow])
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := hP.profile_counts hJ hJ4 hn.le hp
  intro T hT hTJ hT3
  have hmem : T ∈ (hP.below_finite J 3).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hT, hTJ, hT3⟩
  rcases hP.tri3_cases hJ hJ4 hn.le hmem with ht | ht | ht | ht | ht | ht | ht
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr ht)
  · exact False.elim (not_of_filter_card_zero h4 hmem ht)
  · exact False.elim (not_of_filter_card_zero h5 hmem ht)
  · exact False.elim (not_of_filter_card_zero h6 hmem ht)
  · exact False.elim (not_of_filter_card_zero h7 hmem ht)

/-- Only Y can contain a six-vertex ridge in the residual configuration. -/
theorem IsCSPolytope5.fewFull18_one_pair_six_ridge_Y
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F K : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hK : K ∈ faces P) (hKF : K ⊆ F) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6) :
    faceRow P F = excRow := by
  have hm : faceRow P F ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F, Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF, hF4⟩), rfl⟩
  rcases (hP.fewFull18_one_pair_profile hv hh hc hlt).1 _ hm with hY | hJ | hH
  · exact hY
  · have ht := hP.J_three_types hF hF4 hJ K hK hKF hK3
    rcases ht with ht | ht | ht <;> have := congrArg Prod.fst ht <;>
      change cnt P K 0 = _ at this <;> omega
  · have ht := (hP.fewFull18_one_pair_full_types hv hh hc hlt hF hF4 hH).2.2.2 K hK hKF hK3
    rcases ht with ht | ht | ht <;> have := congrArg Prod.fst ht <;>
      change cnt P K 0 = _ at this <;> omega

/-- A Y facet has one partner Y sharing its prism and all its quadrilaterals. -/
theorem IsCSPolytope5.fewFull18_one_pair_Y_partner
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {Y : Set E5} (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hrow : faceRow P Y = excRow) :
    ∃ Z K, Z ∈ faces P ∧ dim Z = 4 ∧ Z ≠ Y ∧ faceRow P Z = excRow ∧
      K ∈ faces P ∧ dim K = 3 ∧ tri3 P K = (6, 9, 5) ∧ K = Y ∩ Z ∧
      (∀ Q ∈ faces P, Q ⊆ Y → dim Q = 2 → cnt P Q 0 = 4 → Q ⊆ Z) ∧
      (∀ T ∈ faces P, dim T = 4 → faceRow P T = excRow → T ≠ Y →
        ∀ Q ∈ faces P, Q ⊆ Y → Q ⊆ T → dim Q = 2 → cnt P Q 0 = 4 → T = Z) := by
  obtain ⟨K, hK, hKY, hK3, ht, -, hbase⟩ := hP.Y_prism_base hY hY4 hrow
  obtain ⟨Z, hZ, hZ4, hZY, hKZ⟩ := hP.exists_other_facet hK hK3 hKY
  have hZrow := hP.fewFull18_one_pair_six_ridge_Y hv hh hc hlt hZ hZ4 hK hKZ hK3
    (congrArg Prod.fst ht)
  have hinter := hP.three_face_eq_inter hY hY4 hZ hZ4 hZY.symm hK hK3 hKY hKZ
  refine ⟨Z, K, hZ, hZ4, hZY, hZrow, hK, hK3, ht, hinter, ?_, ?_⟩
  · intro Q hQ hQY hQ2 hQ4
    exact (hbase Q hQ hQY hQ2 hQ4).trans hKZ
  · intro T hT hT4 hTrow hTY Q hQ hQY hQT hQ2 hQ4
    have hQZ := (hbase Q hQ hQY hQ2 hQ4).trans hKZ
    let S := (hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)
    have hcard : S.card = 2 := hP.fewFull18_one_pair_quad_two_Y hv hh hc hlt hQ hQ2 hQ4
    have hYS : Y ∈ S := by
      simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hY, hQY, hY4⟩, hrow⟩
    have hZS : Z ∈ S := by
      simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hZ, hQZ, hZ4⟩, hZrow⟩
    have hTS : T ∈ S := by
      simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hT, hQT, hT4⟩, hTrow⟩
    have hpair : ({Y, Z} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
      (by intro U hU; rcases Finset.mem_insert.1 hU with rfl | hU
          · exact hYS
          · exact Finset.mem_singleton.1 hU ▸ hZS)
      (by rw [hcard, Finset.card_pair hZY.symm])
    rw [← hpair] at hTS
    rcases Finset.mem_insert.1 hTS with h | h
    · exact False.elim (hTY h)
    · exact Finset.mem_singleton.1 h

end Kalai5
