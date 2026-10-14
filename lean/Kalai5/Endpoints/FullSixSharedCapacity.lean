import Kalai5.Endpoints.FullSixPartnerObstruction
import Kalai5.Endpoints.FullSmallAvoidingCapacity
import Kalai5.Endpoints.FullPairExhaust

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A full facet with at least seven ridges and one full neighbour cannot
miss two distinct antipodal pairs of small facets. -/
theorem IsCSPolytope5.full_six_two_missed_small_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    {F H T X Y : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) (hHr : 7 ≤ cnt P H 3)
    (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hX7 : cnt P X 0 = 7)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hY7 : cnt P Y 0 = 7)
    (hYX : Y ≠ X) (hYnX : Y ≠ -X)
    (hmissX : ∀ S ∈ faces P, dim S = 3 → S ⊆ X → (¬ S ⊆ H) ∧ (¬ S ⊆ -H))
    (hmissY : ∀ S ∈ faces P, dim S = 3 → S ⊆ Y → (¬ S ⊆ H) ∧ (¬ S ⊆ -H)) : False := by
  let full : Set (Set E5) := {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8}
  have hfin : full.Finite := hP.faces_finite.subset fun J hJ => hJ.1
  let D := hfin.toFinset.erase F
  have hDc : D.card = 3 := by
    have hn : hfin.toFinset.card = 4 := by
      rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset]
      exact (hP.cnt8_eq_full_ncard).symm.trans hc
    have hm : F ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 ⟨hF,hF4,hF8⟩
    rw [Finset.card_erase_of_mem hm,hn]
  have hD : ∀ J ∈ D, J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8 := by
    intro J hJ
    exact (Set.Finite.mem_toFinset hfin).1 (Finset.mem_erase.1 hJ).2
  have havoid : ∀ J ∈ D, J ≠ H → ∀ S ∈ faces P, S ⊆ H → dim S = 3 → ¬ S ⊆ J := by
    intro J hJD hJH S hS hSH hS3 hSJ
    obtain ⟨hJ,hJ4,hJ8⟩ := hD J hJD
    have hFnH : F ≠ -H := by intro he; apply hHnF; rw [he,neg_neg]
    have he := hP.full_six_partner_unique hv hc hH hH4 hH8 hF hF4 hF8 hHF.symm hFnH
      hT6 (by rw [hTI,inter_comm]) hJ hJ4 hJ8 hJH ⟨S,hS,hS3,hSH,hSJ⟩
    exact (Finset.mem_erase.1 hJD).1 he
  let es : Set (Set E5) := {X,-X,Y,-Y}
  let E := es.toFinite.toFinset
  have hXnX : X ≠ -X := fun he =>
    (hP.ne_of_dim_ne' (by rw [hX4]; decide)) (hP.eq_of_neg_eq hX he.symm)
  have hYnY : Y ≠ -Y := fun he =>
    (hP.ne_of_dim_ne' (by rw [hY4]; decide)) (hP.eq_of_neg_eq hY he.symm)
  have hXnY : X ≠ -Y := by intro he; apply hYnX; rw [he,neg_neg]
  have hnXnY : -X ≠ -Y := fun he => hYX (neg_injective he).symm
  have hEc : E.card = 4 := by
    rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset]
    exact Set.ncard_eq_four.2 ⟨X,-X,Y,-Y,hXnX,hYX.symm,hXnY,hYnX.symm,hnXnY,hYnY,rfl⟩
  have hE : ∀ J ∈ E, J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 ≠ 8 := by
    intro J hJ
    have hm : J ∈ es := (Set.Finite.mem_toFinset es.toFinite).1 hJ
    rcases hm with rfl | rfl | rfl | rfl
    · exact ⟨hX,hX4,by omega⟩
    · exact ⟨neg_mem_faces hP.symm hX,by rw [dim_neg,hX4],by rw [hP.cnt_neg,hX7]; decide⟩
    · exact ⟨hY,hY4,by omega⟩
    · exact ⟨neg_mem_faces hP.symm hY,by rw [dim_neg,hY4],by rw [hP.cnt_neg,hY7]; decide⟩
  have miss : ∀ {J},
      (∀ S ∈ faces P, dim S = 3 → S ⊆ J → (¬ S ⊆ H) ∧ (¬ S ⊆ -H)) →
      ∀ S ∈ faces P, S ⊆ H → dim S = 3 → (¬ S ⊆ J) ∧ (¬ S ⊆ -J) := by
    intro J hm S hS hSH hS3
    refine ⟨fun hSJ => (hm S hS hS3 hSJ).1 hSH,?_⟩
    intro hnSJ
    have hnSJ' : -S ⊆ J := by simpa using Set.neg_subset_neg.2 hnSJ
    exact (hm (-S) (neg_mem_faces hP.symm hS) (by rw [dim_neg,hS3]) hnSJ').2
      (Set.neg_subset_neg.2 hSH)
  have hmiss : ∀ J ∈ E, ∀ S ∈ faces P, S ⊆ H → dim S = 3 → (¬ S ⊆ J) ∧ (¬ S ⊆ -J) := by
    intro J hJ S hS hSH hS3
    have hm : J ∈ es := (Set.Finite.mem_toFinset es.toFinite).1 hJ
    rcases hm with rfl | rfl | rfl | rfl
    · exact miss hmissX S hS hSH hS3
    · simpa only [neg_neg] using (miss hmissX S hS hSH hS3).symm
    · exact miss hmissY S hS hSH hS3
    · simpa only [neg_neg] using (miss hmissY S hS hSH hS3).symm
  have hb := hP.facet_ridge_capacity_avoiding_small hv hH hH4 D hD havoid E hE hmiss
  omega

/-- A full facet with three six-vertex ridges cannot share one of them
with a full facet having at least seven ridges. -/
theorem IsCSPolytope5.full_three_six_ridges_shared_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hsmall : ∀ X ∈ faces P, dim X = 4 → cnt P X 0 ≠ 8 → cnt P X 0 = 7)
    {F H T U V : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8) (hz : big2 P F = 0)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) (hHr : 7 ≤ cnt P H 3)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    (hU : U ∈ faces P) (hUF : U ⊆ F) (hU3 : dim U = 3) (hU6 : cnt P U 0 = 6) (hUT : U ≠ T)
    (hV : V ∈ faces P) (hVF : V ⊆ F) (hV3 : dim V = 3) (hV6 : cnt P V 0 = 6) (hVT : V ≠ T)
    (hVU : V ≠ U) : False := by
  have hTF : T ⊆ F := hTI ▸ inter_subset_left
  have hiU := hP.six_ridges_inter_four_of_no_big hF8 hz hT hTF hT3 hT6 hU hUF hU3 hU6 hUT.symm
  have hiV := hP.six_ridges_inter_four_of_no_big hF8 hz hT hTF hT3 hT6 hV hVF hV3 hV6 hVT.symm
  obtain ⟨X,hX,hX4,hXF,hUX⟩ := hP.exists_other_facet hU hU3 hUF
  obtain ⟨Y,hY,hY4,hYF,hVY⟩ := hP.exists_other_facet hV hV3 hVF
  have small : ∀ {R X}, R ∈ faces P → R ⊆ F → dim R = 3 → R ≠ T →
      X ∈ faces P → dim X = 4 → X ≠ F → R ⊆ X → cnt P X 0 = 7 := by
    intro R X hR hRF hR3 hRT hX hX4 hXF hRX
    apply hsmall X hX hX4
    intro hX8
    have he := hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8 hHF hHnF
      hT6 hTI hX hX4 hX8 hXF ⟨R,hR,hR3,hRF,hRX⟩
    exact hRT ((hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hR hR3 hRF (he ▸ hRX)).trans hTI.symm)
  have hX7 := small hU hUF hU3 hUT hX hX4 hXF hUX
  have hY7 := small hV hVF hV3 hVT hY hY4 hYF hVY
  have hYX : Y ≠ X := by
    intro he
    have hUI := hP.three_face_eq_inter hF hF4 hX hX4 hXF.symm hU hU3 hUF hUX
    have hVI := hP.three_face_eq_inter hF hF4 hX hX4 hXF.symm hV hV3 hVF (he ▸ hVY)
    exact hVU (hVI.trans hUI.symm)
  have hYnX : Y ≠ -X := by
    intro he
    have hd := Set.disjoint_of_subset hUX (he ▸ hVY) (hP.facet_disjoint_neg hX hX4)
    have hb := hP.cnt_zero_add_le_of_disjoint hUF hVF hd
    omega
  exact hP.full_six_two_missed_small_false hv hh hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hHr hT6 hTI
    hX hX4 hX7 hY hY4 hY7 hYX hYnX
    (hP.full_six_partner_avoids_both hv hF hF4 hF8 hH hH4 hH8 hT hT3 hT6 hTI hUF hU6 hiU hX hX4 hX7 hUX)
    (hP.full_six_partner_avoids_both hv hF hF4 hF8 hH hH4 hH8 hT hT3 hT6 hTI hVF hV6 hiV hY hY4 hY7 hVY)

end Kalai5
