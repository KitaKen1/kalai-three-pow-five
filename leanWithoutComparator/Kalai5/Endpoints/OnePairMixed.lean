import Kalai5.Endpoints.OnePairMeets

/-!
# The mixed quadrilaterals lead to J facets

There are only two eight-vertex facets, an antipodal pair. A prism attached
to a quadrilateral of H has two other quadrilaterals. Each belongs to neither
H nor -H, and therefore has J as its third facet. J contains just one
quadrilateral, so different mixed quadrilaterals give different J facets.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- With exactly two eight-vertex facets, they are an antipodal pair. -/
lemma IsCSPolytope5.two_full_facets_eq_or_neg (hc : cnt8 (facetRows P) = 2)
    {H X : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX8 : cnt P X 0 = 8) : X = H ∨ X = -H := by
  let S := (hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)
  have hn : S.card = 2 := by
    have he : cnt8 (facetRows P) = S.card := by
      rw [cnt8, length_filter_eq_sum, hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0)]
      simp only [S, Finset.card_filter]
      rfl
    omega
  have hneg : -H ≠ H := fun he =>
    (hP.ne_of_dim_ne' (by rw [hH4]; decide)) (hP.eq_of_neg_eq hH he)
  have hHS : H ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hH, hH4⟩, hH8⟩
  have hNS : -H ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨neg_mem_faces hP.symm hH, by rw [dim_neg, hH4]⟩, by rw [hP.cnt_neg, hH8]⟩
  have hXS : X ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hX, hX4⟩, hX8⟩
  have heq : ({H, -H} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
    (by intro F hF; rcases Finset.mem_insert.1 hF with rfl | hF
        · exact hHS
        · exact Finset.mem_singleton.1 hF ▸ hNS)
    (by rw [hn, Finset.card_pair hneg.symm])
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hXS
  exact hXS

/-- A J facet contains exactly one quadrilateral. -/
theorem IsCSPolytope5.J_quad_count {J : Set E5}
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hrow : faceRow P J = OnePairProfile.jRow) :
    q4 P J = 1 := by
  have hn : cnt P J 0 = 7 := congrArg Row.n hrow
  obtain ⟨hm, he⟩ := hP.facet_rowX hJ hJ4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 = OnePairProfile.jRow →
      X.2.1 = [3, 2, 2, 0, 0, 0, 0] := by decide +kernel
  have hp := hcheck _ hm (by change rowOf J = _; rw [he, hrow])
  have hc := (hP.profile_counts hJ hJ4 hn.le hp).2.1
  have hsum := hP.two_q4_facet hJ hJ4
  have ht : ∀ T ∈ (hP.below_finite J 3).toFinset,
      (q4 P T : ℤ) = if tri3 P T = (5, 8, 5) then 1 else 0 := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    rcases hP.J_three_types hJ hJ4 hrow T hT.1 hT.2.1 hT.2.2 with h | h | h
    · rw [hP.q4_464 hT.1 hT.2.2 h, h]; norm_num
    · rw [(hP.q4_585 hT.1 hT.2.2 h).1, h]; norm_num
    · rw [(hP.q4_596 hT.1 hT.2.2 h).1, h]; norm_num
  rw [Finset.sum_congr rfl ht, Finset.sum_boole, hc] at hsum
  omega

/-- A J facet cannot receive two different mixed quadrilaterals. -/
lemma IsCSPolytope5.J_quad_unique {J Q R : Set E5}
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hrow : faceRow P J = OnePairProfile.jRow)
    (hQ : Q ∈ faces P) (hQJ : Q ⊆ J) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRJ : R ⊆ J) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) : Q = R := by
  obtain ⟨U, hU⟩ := Set.ncard_eq_one.1 (hP.J_quad_count hJ hJ4 hrow)
  have hq : Q ∈ {T | T ∈ faces P ∧ T ⊆ J ∧ dim T = 2 ∧ cnt P T 0 = 4} :=
    ⟨hQ, hQJ, hQ2, hQ4⟩
  have hr : R ∈ {T | T ∈ faces P ∧ T ⊆ J ∧ dim T = 2 ∧ cnt P T 0 = 4} :=
    ⟨hR, hRJ, hR2, hR4⟩
  rw [hU, Set.mem_singleton_iff] at hq hr
  exact hq.trans hr.symm

/-- A second quadrilateral of the prism attached to H belongs to neither
of the two full facets, so its third facet must be J. -/
theorem IsCSPolytope5.fewFull18_one_pair_mixed_quad_J
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {H Y K Q R : Set E5}
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHrow : faceRow P H = OnePairProfile.fullRow 20)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hKY : K ⊆ Y) (hK6 : cnt P K 0 = 6)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R) :
    ¬ R ⊆ H ∧ ¬ R ⊆ -H ∧
      ∃ J, J ∈ faces P ∧ dim J = 4 ∧ faceRow P J = OnePairProfile.jRow ∧ R ⊆ J := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHrow
  have hY7 : cnt P Y 0 = 7 := congrArg Row.n hYrow
  have hHY : H ≠ Y := by intro he; rw [he] at hH8; omega
  have hnH : ¬ R ⊆ H := by
    intro hRH
    exact hQR (hP.fewFull18_one_pair_H_shared_quad_unique hv hh hc hlt
      hH hH4 hHrow hY hY4 hHY hQ hQH (hQK.trans hKY) hQ2 hQ4
      hR hRH (hRK.trans hKY) hR2 hR4)
  have hnN : ¬ R ⊆ -H := by
    intro hRN
    have hdisj := hP.disjoint_neg_of_full hH (hP.ne_of_dim_ne' (by rw [hH4]; decide)) (by omega)
    have hi := (hP.six_vertex_quad_pair hK6 hQ hQK hQ2 hQ4 hR hRK hR2 hR4 hQR).2.1
    obtain ⟨v, hvQ, hvR⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hi]; decide)
    obtain ⟨x, hx⟩ := hvQ.1.1
    exact Set.disjoint_left.1 hdisj (hQH (hvQ.2.1 hx)) (hRN (hvR.2.1 hx))
  refine ⟨hnH, hnN, ?_⟩
  let S := (hP.above_finite R 4).toFinset
  have hthree : S.card = 3 := by
    have h := hP.quad_up_eq_three_of_G_eq_zero
      (hP.fewFull18_one_pair_stresses hv hh hc hlt).1 hR hR2 hR4
    rwa [Set.ncard_eq_toFinset_card _ (hP.above_finite R 4)] at h
  have htwo : (S.filter fun F => faceRow P F = excRow).card = 2 :=
    hP.fewFull18_one_pair_quad_two_Y hv hh hc hlt hR hR2 hR4
  obtain ⟨J, hJS, hnY⟩ : ∃ J ∈ S, faceRow P J ≠ excRow := by
    by_contra hno
    push Not at hno
    have hf : S.filter (fun F => faceRow P F = excRow) = S := Finset.filter_eq_self.2 hno
    rw [hf, hthree] at htwo
    omega
  change J ∈ (hP.above_finite R 4).toFinset at hJS
  rw [Set.Finite.mem_toFinset] at hJS
  have hm : faceRow P J ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨J, Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hJS.1, hJS.2.2⟩), rfl⟩
  rcases (hP.fewFull18_one_pair_profile hv hh hc hlt).1 _ hm with h | h | h
  · exact False.elim (hnY h)
  · exact ⟨J, hJS.1, hJS.2.2, h, hJS.2.1⟩
  · rcases hP.two_full_facets_eq_or_neg hc hH hH4 hH8 hJS.1 hJS.2.2
        (congrArg Row.n h) with he | he
    · exact False.elim (hnH (he ▸ hJS.2.1))
    · exact False.elim (hnN (he ▸ hJS.2.1))

end Kalai5
