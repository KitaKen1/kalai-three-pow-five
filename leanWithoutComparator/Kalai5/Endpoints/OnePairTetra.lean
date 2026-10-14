import Kalai5.Endpoints.OnePairSigned

/-!
# Each mixed quadrilateral gives a tetrahedron in H

The two prism partners contribute their extra vertices to both H and J.
Antipodal counting makes H ∩ J a four-vertex face. It cannot be a polygon,
because J's unique quadrilateral is the mixed one. Thus it is a tetrahedron.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Four common vertices and a different quadrilateral of J force a
tetrahedral intersection of two facets. -/
lemma IsCSPolytope5.J_four_vertex_inter_tetra {H J R : Set E5}
    (hH : H ∈ faces P) (_hH4 : dim H = 4)
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hrow : faceRow P J = OnePairProfile.jRow)
    (hcnt : cnt P (H ∩ J) 0 = 4)
    (hR : R ∈ faces P) (hRJ : R ⊆ J) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4)
    (hnH : ¬ R ⊆ H) :
    H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
  have hne : (H ∩ J).Nonempty := by
    obtain ⟨v, hv⟩ := Set.nonempty_of_ncard_ne_zero
      (show (vset P (H ∩ J)).ncard ≠ 0 by rw [← cnt_eq_vset, hcnt]; decide)
    exact hv.1.1.mono hv.2.1
  have hI := inter_mem_faces_of_nonempty hH hJ hne
  have hIJ : H ∩ J ∈ faces J := mem_faces_of_subset (face_subset hJ) hI inter_subset_right
  have hneJ : H ∩ J ≠ J := by
    intro he
    exact hnH (hRJ.trans (by rw [← he]; exact inter_subset_left))
  have hdim := dim_lt_of_mem_faces_ne hIJ hneJ
  have h3 : dim (H ∩ J) = 3 := by
    by_contra hn3
    by_cases h2 : dim (H ∩ J) = 2
    · have he := hP.J_quad_unique hJ hJ4 hrow hI inter_subset_right h2 hcnt hR hRJ hR2 hR4
      exact hnH (he ▸ inter_subset_left)
    · have := hP.cnt_le_two_of_dim_le_one hI (by omega)
      omega
  refine ⟨hI, h3, ?_⟩
  rcases hP.J_three_types hJ hJ4 hrow (H ∩ J) hI inter_subset_right h3 with h | h | h
  · exact h
  · have hh : cnt P (H ∩ J) 0 = 5 := congrArg Prod.fst h; omega
  · have hh : cnt P (H ∩ J) 0 = 5 := congrArg Prod.fst h; omega

/-- Every other quadrilateral of the Y-pair prism gives a J facet meeting
H in a tetrahedron. This packages the local construction for the final count. -/
theorem IsCSPolytope5.fewFull18_one_pair_mixed_tetra
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {H Y Z K Q R : Set E5}
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHrow : faceRow P H = OnePairProfile.fullRow 20)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hZrow : faceRow P Z = excRow) (hYZ : Y ≠ Z)
    (hK : K ∈ faces P) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6) (hKI : K = Y ∩ Z)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R) :
    ∃ J, J ∈ faces P ∧ dim J = 4 ∧ faceRow P J = OnePairProfile.jRow ∧ R ⊆ J ∧
      H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHrow
  have hY7 : cnt P Y 0 = 7 := congrArg Row.n hYrow
  have hZ7 : cnt P Z 0 = 7 := congrArg Row.n hZrow
  have hHY : H ≠ Y := by intro he; rw [he] at hH8; omega
  have hHZ : H ≠ Z := by intro he; rw [he] at hH8; omega
  have hKI' : K = Z ∩ Y := by rw [hKI, Set.inter_comm]
  obtain ⟨hnH, -, J, hJ, hJ4, hJrow, hRJ⟩ :=
    hP.fewFull18_one_pair_mixed_quad_J hv hh hc hlt hH hH4 hHrow hY hY4 hYrow
      (hKI ▸ inter_subset_left) hK6 hQ hQK hQH hQ2 hQ4 hR hRK hR2 hR4 hQR
  have hJY : J ≠ Y := by
    intro he
    have h := hJrow
    rw [he, hYrow] at h
    exact (by decide : excRow ≠ OnePairProfile.jRow) h
  have hJZ : J ≠ Z := by
    intro he
    have h := hJrow
    rw [he, hZrow] at h
    exact (by decide : excRow ≠ OnePairProfile.jRow) h
  have hA := hP.fewFull18_one_pair_Y_apex_in_third hv hh hc hlt hY hY4 hYrow
    hZ hZ4 hYZ hK hK3 hK6 hKI hH hH4 hHY hHZ hQ hQK hQH hQ2 hQ4
  have hB := hP.fewFull18_one_pair_Y_apex_in_third hv hh hc hlt hZ hZ4 hZrow
    hY hY4 hYZ.symm hK hK3 hK6 hKI' hH hH4 hHZ hHY hQ hQK hQH hQ2 hQ4
  have hAJ := hP.fewFull18_one_pair_Y_apex_in_third hv hh hc hlt hY hY4 hYrow
    hZ hZ4 hYZ hK hK3 hK6 hKI hJ hJ4 hJY hJZ hR hRK hRJ hR2 hR4
  have hBJ := hP.fewFull18_one_pair_Y_apex_in_third hv hh hc hlt hZ hZ4 hZrow
    hY hY4 hYZ.symm hK hK3 hK6 hKI' hJ hJ4 hJZ hJY hR hRK hRJ hR2 hR4
  have hcnt := hP.mixed_J_four_vertices hv
    hH (hP.ne_of_dim_ne' (by rw [hH4]; decide))
    hY (hP.ne_of_dim_ne' (by rw [hY4]; decide)) hY7
    hZ (hP.ne_of_dim_ne' (by rw [hZ4]; decide)) hZ7 hKI hK6
    hA.2.2.2.2 hB.2.2.2.2 hA.2.2.1 hQ4
    (hP.six_vertex_quad_pair hK6 hQ hQK hQ2 hQ4 hR hRK hR2 hR4 hQR).1 hR4
    hJ (hP.ne_of_dim_ne' (by rw [hJ4]; decide)) hAJ.2.1 hBJ.2.1 hAJ.2.2.1
  exact ⟨J, hJ, hJ4, hJrow, hRJ, hP.J_four_vertex_inter_tetra hH hH4 hJ hJ4 hJrow
    hcnt hR hRJ hR2 hR4 hnH⟩

end Kalai5
