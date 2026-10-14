import Kalai5.Endpoints.TwoPairZeroBGeometry

/-! Mixed quadrilaterals force tetrahedral ridges, including when their
third facet is D or H21 instead of J. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.two_pair_zero_mixed_quad_small
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {H Y K Q R : Set E5}
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHrow : faceRow P H = OnePairProfile.fullRow 20)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hKY : K ⊆ Y) (hK6 : cnt P K 0 = 6)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R) :
    ¬ R ⊆ H ∧ ¬ R ⊆ -H ∧
      ∃ J, J ∈ faces P ∧ dim J = 4 ∧ q4 P J ≤ 1 ∧ R ⊆ J := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHrow
  have hY7 : cnt P Y 0 = 7 := congrArg Row.n hYrow
  have hHY : H ≠ Y := by intro he; rw [he] at hH8; omega
  have hnH : ¬ R ⊆ H := by
    intro hRH
    exact hQR (hP.two_pair_zero_H_shared_quad_unique hv hh hc hG hlt
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
      hG hR hR2 hR4
    rwa [Set.ncard_eq_toFinset_card _ (hP.above_finite R 4)] at h
  have htwo : (S.filter fun F => faceRow P F = excRow).card = 2 :=
    hP.two_pair_zero_quad_two_Y hv hh hc hG hlt hR hR2 hR4
  obtain ⟨J, hJS, hnY⟩ : ∃ J ∈ S, faceRow P J ≠ excRow := by
    by_contra hno
    push Not at hno
    have hf : S.filter (fun F => faceRow P F = excRow) = S := Finset.filter_eq_self.2 hno
    rw [hf, hthree] at htwo
    omega
  change J ∈ (hP.above_finite R 4).toFinset at hJS
  rw [Set.Finite.mem_toFinset] at hJS
  have hnH20 : faceRow P J ≠ OnePairProfile.fullRow 20 := by
    intro h
    rcases hP.two_pair_zero_H20_eq_or_neg hv hh hc hG hlt hH hH4 hHrow
        hJS.1 hJS.2.2 h with he | he
    · exact hnH (he ▸ hJS.2.1)
    · exact hnN (he ▸ hJS.2.1)
  exact ⟨J,hJS.1,hJS.2.2,
    hP.two_pair_zero_other_quad_le_one hv hh hc hG hlt hJS.1 hJS.2.2 hnY hnH20,hJS.2.1⟩

theorem IsCSPolytope5.two_pair_zero_mixed_tetra
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) (hlt : (faces P).ncard < 243)
    {H Y Z K Q R : Set E5}
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHrow : faceRow P H = OnePairProfile.fullRow 20)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hZrow : faceRow P Z = excRow) (hYZ : Y ≠ Z)
    (hK : K ∈ faces P) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6) (hKI : K = Y ∩ Z)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R) :
    ∃ J, J ∈ faces P ∧ dim J = 4 ∧ q4 P J ≤ 1 ∧ R ⊆ J ∧
      H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHrow
  have hY7 : cnt P Y 0 = 7 := congrArg Row.n hYrow
  have hZ7 : cnt P Z 0 = 7 := congrArg Row.n hZrow
  have hHY : H ≠ Y := by intro he; rw [he] at hH8; omega
  have hHZ : H ≠ Z := by intro he; rw [he] at hH8; omega
  have hKI' : K = Z ∩ Y := by rw [hKI, Set.inter_comm]
  obtain ⟨hnH, -, J, hJ, hJ4, hJrow, hRJ⟩ :=
    hP.two_pair_zero_mixed_quad_small hv hh hc hG hlt hH hH4 hHrow hY hY4 hYrow
      (hKI ▸ inter_subset_left) hK6 hQ hQK hQH hQ2 hQ4 hR hRK hR2 hR4 hQR
  have hJY : J ≠ Y := by
    intro he
    have hy := (hP.Y_quad hY hY4 hYrow).1
    rw [he] at hJrow
    omega
  have hJZ : J ≠ Z := by
    intro he
    have hz := (hP.Y_quad hZ hZ4 hZrow).1
    rw [he] at hJrow
    omega
  have hA := hP.Y_apex_in_third_of_G_zero hv hG hY hY4 hYrow
    hZ hZ4 hYZ hK hK3 hK6 hKI hH hH4 hHY hHZ hQ hQK hQH hQ2 hQ4
  have hB := hP.Y_apex_in_third_of_G_zero hv hG hZ hZ4 hZrow
    hY hY4 hYZ.symm hK hK3 hK6 hKI' hH hH4 hHZ hHY hQ hQK hQH hQ2 hQ4
  have hAJ := hP.Y_apex_in_third_of_G_zero hv hG hY hY4 hYrow
    hZ hZ4 hYZ hK hK3 hK6 hKI hJ hJ4 hJY hJZ hR hRK hRJ hR2 hR4
  have hBJ := hP.Y_apex_in_third_of_G_zero hv hG hZ hZ4 hZrow
    hY hY4 hYZ.symm hK hK3 hK6 hKI' hJ hJ4 hJZ hJY hR hRK hRJ hR2 hR4
  have hcnt := hP.mixed_J_four_vertices hv
    hH (hP.ne_of_dim_ne' (by rw [hH4]; decide))
    hY (hP.ne_of_dim_ne' (by rw [hY4]; decide)) hY7
    hZ (hP.ne_of_dim_ne' (by rw [hZ4]; decide)) hZ7 hKI hK6
    hA.2.2.2.2 hB.2.2.2.2 hA.2.2.1 hQ4
    (hP.six_vertex_quad_pair hK6 hQ hQK hQ2 hQ4 hR hRK hR2 hR4 hQR).1 hR4
    hJ (hP.ne_of_dim_ne' (by rw [hJ4]; decide)) hAJ.2.1 hBJ.2.1 hAJ.2.2.1
  exact ⟨J, hJ, hJ4, hJrow, hRJ, hP.four_vertex_inter_tetra_of_quad_le_one hH hH4 hJ hJ4 hJrow
    hcnt hR hRJ hR2 hR4 hnH⟩

end Kalai5
