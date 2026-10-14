import Kalai5.Endpoints.FullPyramidNonadjacent
import Kalai5.Endpoints.PyramidTriangleCount
import Kalai5.Endpoints.FullPairExhaust
import Kalai5.Endpoints.FullRidgeSaturation

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Under saturated full degree, a triangle-intersecting square pyramid
forces a nonadjacent tetrahedron in the opposite full neighbour. -/
theorem IsCSPolytope5.full_six_pyramid_triangle_partner
    (hv : fvec P 0 = 16) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hdeg : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 →
      {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
        ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X}.ncard = 2)
    {F H T R : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3)
    (hR5 : cnt P R 0 = 5) (hi3 : cnt P (T ∩ R) 0 = 3) :
    ∃ X S, X ∈ faces P ∧ dim X = 4 ∧ cnt P X 0 = 7 ∧ X ≠ F ∧ R ⊆ X ∧
      S ∈ faces P ∧ dim S = 3 ∧ S ⊆ X ∧ S ⊆ -H ∧ cnt P S 0 = 4 ∧ dim (-T ∩ S) ≠ 2 := by
  obtain ⟨X,hX,hX4,hXF,hRX⟩ := hP.exists_other_facet hR hR3 hRF
  have hX8 : cnt P X 0 ≠ 8 := by
    intro h8
    have hXH := hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hT6 hTI
      hX hX4 h8 hXF ⟨R,hR,hR3,hRF,hRX⟩
    have he : R = T := (hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hR hR3
      hRF (hXH ▸ hRX)).trans hTI.symm
    rw [he] at hR5
    omega
  have hX7 := hsmall X hX hX4 hX8
  have hobs := hP.full_pyramid_partner_nonadjacent hv hF hF4 hF8 hH hH4 hH8
    hT hT3 hT6 hTI hRF hR5 hi3 hX hX4 hX7 hRX
  have hex : ∃ S ∈ faces P, dim S = 3 ∧ S ⊆ -H ∧ S ⊆ X := by
    by_contra hn
    have hs : {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
        ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X} ⊆ {F} := by
      rintro J ⟨hJ,hJ4,hJ8,U,hU,hU3,hUJ,hUX⟩
      rcases hP.four_full_exhaust hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hJ hJ4 hJ8 with
        he | he | he | he
      · exact he
      · have hd := hP.disjoint_neg_of_full hF (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (by omega)
        have hRU : Disjoint R U := Set.disjoint_of_subset hRF (he ▸ hUJ) hd
        have := hP.eight_le_cnt_of_disjoint hX hR hR3 hU hU3 hRX hUX hRU
        omega
      · exact False.elim ((hobs U hU hU3 hUX).1 (he ▸ hUJ))
      · exact False.elim (hn ⟨U,hU,hU3,he ▸ hUJ,hUX⟩)
    have hb := Set.ncard_le_ncard hs (Set.finite_singleton F)
    rw [hdeg X hX hX4 hX8,Set.ncard_singleton] at hb
    omega
  obtain ⟨S,hS,hS3,hSH,hSX⟩ := hex
  obtain ⟨hS4,hnS⟩ := (hobs S hS hS3 hSX).2 hSH
  exact ⟨X,S,hX,hX4,hX7,hXF,hRX,hS,hS3,hSX,hSH,hS4,hnS⟩

/-- One available nonadjacent slot permits at most one square pyramid
meeting the shared ridge in a triangle. -/
theorem IsCSPolytope5.full_six_pyramid_triangle_unique
    (hv : fvec P 0 = 16) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hdeg : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 →
      {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
        ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X}.ncard = 2)
    {F H T R U : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    (hslots : cnt P H 3 ≤ cnt P T 2 + 2)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3)
    (hR5 : cnt P R 0 = 5) (hiR : cnt P (T ∩ R) 0 = 3)
    (hU : U ∈ faces P) (hUF : U ⊆ F) (hU3 : dim U = 3)
    (hU5 : cnt P U 0 = 5) (hiU : cnt P (T ∩ U) 0 = 3) : R = U := by
  obtain ⟨X,S,hX,hX4,hX7,hXF,hRX,hS,hS3,hSX,hSH,hS4,hnS⟩ :=
    hP.full_six_pyramid_triangle_partner hv hc hsmall hdeg hF hF4 hF8 hH hH4 hH8
      hHF hHnF hT hT3 hT6 hTI hR hRF hR3 hR5 hiR
  obtain ⟨Y,V,hY,hY4,hY7,hYF,hUY,hV,hV3,hVY,hVH,hV4,hnV⟩ :=
    hP.full_six_pyramid_triangle_partner hv hc hsmall hdeg hF hF4 hF8 hH hH4 hH8
      hHF hHnF hT hT3 hT6 hTI hU hUF hU3 hU5 hiU
  have hnH : -H ∈ faces P := neg_mem_faces hP.symm hH
  have hnH4 : dim (-H) = 4 := by rw [dim_neg,hH4]
  have hnT : -T ∈ faces P := neg_mem_faces hP.symm hT
  have hnTH : -T ⊆ -H := Set.neg_subset_neg.2 (hTI ▸ inter_subset_right)
  have hnT3 : dim (-T) = 3 := by rw [dim_neg,hT3]
  have hSnT : S ≠ -T := by intro he; rw [he,hP.cnt_neg,hT6] at hS4; omega
  have hVnT : V ≠ -T := by intro he; rw [he,hP.cnt_neg,hT6] at hV4; omega
  have hSV := hP.ridge_nonadjacent_unique hnH hnH4 hnT hnTH hnT3
    (by simpa only [hP.cnt_neg] using hslots)
    hS hSH hS3 hSnT hnS hV hVH hV3 hVnT hnV
  have hXH : X ≠ -H := by intro he; rw [he,hP.cnt_neg,hH8] at hX7; omega
  have hYH : Y ≠ -H := by intro he; rw [he,hP.cnt_neg,hH8] at hY7; omega
  have hXY := hP.ridge_neighbour_unique hnH hnH4 hX hX4 hXH hY hY4 hYH
    hS hS3 hSH hSX (hSV.symm ▸ hVY)
  have hRI := hP.three_face_eq_inter hF hF4 hX hX4 hXF.symm hR hR3 hRF hRX
  have hUI := hP.three_face_eq_inter hF hF4 hX hX4 hXF.symm hU hU3 hUF (hXY.symm ▸ hUY)
  exact hRI.trans hUI.symm

/-- This quantitative replacement for a universal shared ridge is enough
when the other full facet has only one nonadjacent slot. -/
theorem IsCSPolytope5.full_six_pyramid_count_le
    (hv : fvec P 0 = 16) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hdeg : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 →
      {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 ∧
        ∃ U ∈ faces P, dim U = 3 ∧ U ⊆ J ∧ U ⊆ X}.ncard = 2)
    {F H T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    (hslots : cnt P H 3 ≤ cnt P T 2 + 2) :
    tcnt P F (5,8,5) ≤ q4 P T + 1 := by
  apply hP.pyramid_count_le_quad_add_one hF hF4 hF8 hT (hTI ▸ inter_subset_left) hT3 hT6
  intro R hR hRF hR3 htR hiR U hU hUF hU3 htU hiU
  exact hP.full_six_pyramid_triangle_unique hv hc hsmall hdeg hF hF4 hF8 hH hH4 hH8
    hHF hHnF hT hT3 hT6 hTI hslots
    hR hRF hR3 (congrArg Prod.fst htR) hiR hU hUF hU3 (congrArg Prod.fst htU) hiU

end Kalai5

