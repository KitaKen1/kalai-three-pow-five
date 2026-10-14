import Kalai5.Endpoints.G2S2NineQWeights

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Each required six-vertex ridge of either full pair must be shared
with the sole A pair. The full pairs can only share tetrahedra. -/
theorem IsCSPolytope5.g2s2_nine_q_6106_partner_a
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S4.bRow ∨ faceRow P F = G2S2.qRow)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,10,6)) :
    ∃ A, A ∈ faces P ∧ dim A = 4 ∧ faceRow P A = G2S4.aRow ∧ T ⊆ A := by
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hF8 : cnt P F 0 = 8 := by rcases hR with h | h <;> exact congrArg Row.n h
  have hpos := hP.one_le_tcnt hT hTH hT3
  rw [ht] at hpos
  rcases hP.g2s2_nine_q_row_cases hp hH hH4 with hY | hA | hB | hQ
  · have hz := (hP.small_special_free_counts hH hH4 (by rw [hY]; decide +kernel)).1
    omega
  · exact ⟨H,hH,hH4,hA,hTH⟩
  · rcases hR with hFB | hFQ
    · exact False.elim ((hP.unique_pair_ridge_partner_row_ne hp (by decide +kernel)
        hF h4 hFB hH hH4 hHF hT hTF hTH) hB)
    · exact False.elim (hP.full_nine_large_ridge_partner_nonfull hv hh hc hF h4 hF8
        (congrArg Row.r hFQ) hT hTF hT3 (by omega) hH hH4 hHF hTH (congrArg Row.n hB))
  · rcases hR with hFB | hFQ
    · exact False.elim (hP.full_nine_large_ridge_partner_nonfull hv hh hc hH hH4
        (congrArg Row.n hQ) (congrArg Row.r hQ) hT hTH hT3 (by omega)
        hF h4 hHF.symm hTF hF8)
    · exact False.elim ((hP.unique_pair_ridge_partner_row_ne hp (by decide +kernel)
        hF h4 hFQ hH hH4 hHF hT hTF hTH) hQ)

/-- The two full pairs compete for the unique six-vertex ridge in A.
Identifying those ridges would give a forbidden full/full large ridge. -/
theorem IsCSPolytope5.g2s2_nine_q_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.nineQPairs ++ G2S2.nineQPairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 144) : False := by
  obtain ⟨B,hB,hB4,hBR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _
    (by decide +kernel : G2S4.bRow ∈ G2S2.nineQPairs)))
  obtain ⟨Q,hQ,hQ4,hQR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _
    (by decide +kernel : G2S2.qRow ∈ G2S2.nineQPairs)))
  obtain ⟨T,hT,hTB,hT3,ht⟩ := hP.exists_of_tcnt (hP.g2s2_nine_q_full_6106_positive hv hh hc hp hb hB hB4 (Or.inl hBR))
  obtain ⟨U,hU,hUQ,hU3,hu⟩ := hP.exists_of_tcnt (hP.g2s2_nine_q_full_6106_positive hv hh hc hp hb hQ hQ4 (Or.inr hQR))
  obtain ⟨A,hA,hA4,hAR,hTA⟩ := hP.g2s2_nine_q_6106_partner_a hv hh hc hp hB hB4 (Or.inl hBR) hT hTB hT3 ht
  obtain ⟨C,hC,hC4,hCR,hUC⟩ := hP.g2s2_nine_q_6106_partner_a hv hh hc hp hQ hQ4 (Or.inr hQR) hU hUQ hU3 hu
  have hA7 : cnt P A 0 = 7 := congrArg Row.n hAR
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hU6 : cnt P U 0 = 6 := congrArg Prod.fst hu
  have hB8 : cnt P B 0 = 8 := congrArg Row.n hBR
  have hBr : cnt P B 3 = 8 := congrArg Row.r hBR
  have hQ8 : cnt P Q 0 = 8 := congrArg Row.n hQR
  have hQr : cnt P Q 3 = 9 := congrArg Row.r hQR
  have htwo : ((facetRows P).map fun R => if R = G2S4.aRow then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq]
    decide +kernel
  have hfree := hP.g2s2_nine_q_no_big hv hh hc hp A
  rcases hP.two_row_facets_eq_or_neg htwo hA hA4 hAR hC hC4 hCR with he | he
  · have hTU := hP.six_vertex_ridge_unique_of_seven_no_big hA7 hfree hT hTA hT3 hT6
      hU (he ▸ hUC) hU3 hU6
    exact hP.full_nine_large_ridge_partner_nonfull hv hh hc hQ hQ4 hQ8 hQr hT
      (by rw [hTU]; exact hUQ) hT3 (by omega) hB hB4 (by intro he; rw [he,hQr] at hBr; omega) hTB hB8
  · have hnUA : -U ⊆ A := by
      have hs := Set.neg_subset_neg.2 hUC
      rwa [he,neg_neg] at hs
    have hTU := hP.six_vertex_ridge_unique_of_seven_no_big hA7 hfree hT hTA hT3 hT6
      (neg_mem_faces hP.symm hU) hnUA (by rw [dim_neg,hU3]) (by rw [hP.cnt_neg,hU6])
    have hTnQ : T ⊆ -Q := by rw [hTU]; exact Set.neg_subset_neg.2 hUQ
    exact hP.full_nine_large_ridge_partner_nonfull hv hh hc (neg_mem_faces hP.symm hQ)
      (by rw [dim_neg,hQ4]) (by rw [hP.cnt_neg,hQ8]) (by rw [hP.cnt_neg,hQr])
      hT hTnQ hT3 (by omega) hB hB4
      (by intro he; rw [he,hP.cnt_neg,hQr] at hBr; omega) hTB hB8

end Kalai5
