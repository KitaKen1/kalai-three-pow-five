import Kalai5.Endpoints.FullSixSharedCapacity
import Kalai5.Endpoints.FullPyramidObstruction

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The two other six-vertex ridges of R35 exhaust more missed-pair
capacity than a full neighbour with seven or more ridges permits. -/
theorem IsCSPolytope5.r35_6106_partner_nonfull
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    (hr : ∀ H ∈ faces P, dim H = 4 → cnt P H 0 = 8 → 7 ≤ cnt P H 3)
    {F T H : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4) (hFR : faceRow P F = r35Row)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,10,6))
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHF : H ≠ F) (hTH : T ⊆ H) : cnt P H 0 ≠ 8 := by
  intro hH8
  have hmod : fvec P 4 % 4 = 2 := by rw [hh]
  have hn : cnt P F 0 = 8 := congrArg Row.n hFR
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hTI := hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hT hT3 hTF hTH
  have hHnF : H ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hT.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4) (hTF hx) (he ▸ hTH hx)
  have hm : r35Row ∈ facetRows P := by
    rw [← hFR]
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F,Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF,hF4⟩),rfl⟩
  have hz := hP.big2_zero_of_r35_sixteen_mod_four hv hmod hm F
  obtain ⟨hpr,h610⟩ := hP.r35_six_ridge_counts_of_sixteen_mod_four hv hmod hF hF4 hFR
  obtain ⟨U,W,hUW,hU,hW⟩ := hP.exists_two_of_tcnt (by omega : 2 ≤ tcnt P F (6,10,6))
  have hex : ∃ U, U ∈ faces P ∧ U ⊆ F ∧ dim U = 3 ∧ tri3 P U = (6,10,6) ∧ U ≠ T := by
    by_cases he : U = T
    · exact ⟨W,hW.1,hW.2.1,hW.2.2.1,hW.2.2.2,by intro he'; exact hUW (he.trans he'.symm)⟩
    · exact ⟨U,hU.1,hU.2.1,hU.2.2.1,hU.2.2.2,he⟩
  obtain ⟨U,hU,hUF,hU3,hu,hUT⟩ := hex
  obtain ⟨V,hV,hVF,hV3,hvT⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,9,5))
  have hVT : V ≠ T := by intro he; rw [he,ht] at hvT; contradiction
  have hVU : V ≠ U := by intro he; rw [he,hu] at hvT; contradiction
  exact hP.full_three_six_ridges_shared_false hv hh hc hsmall hF hF4 hn hz hH hH4 hH8 hHF hHnF
    (hr H hH hH4 hH8) hT hT3 hT6 hTI hU hUF hU3 (congrArg Prod.fst hu) hUT
    hV hVF hV3 (congrArg Prod.fst hvT) hVT hVU

end Kalai5
