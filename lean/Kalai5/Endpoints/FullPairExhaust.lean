import Kalai5.Endpoints.FullCrossVertices

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.cnt8_eq_full_ncard : cnt8 (facetRows P) =
    {F | F ∈ faces P ∧ dim F = 4 ∧ cnt P F 0 = 8}.ncard := by
  have hc : cnt8 (facetRows P) =
      ((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card := by
    rw [cnt8,length_filter_eq_sum,hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0),
      Finset.card_filter]
    rfl
  rw [hc,← Set.ncard_coe_finset]
  congr 1
  ext F
  simp only [Finset.mem_coe,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  tauto

theorem IsCSPolytope5.four_full_exhaust (hc : cnt8 (facetRows P) = 4)
    {F H : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    {J : Set E5} (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hJ8 : cnt P J 0 = 8) :
    J = F ∨ J = -F ∨ J = H ∨ J = -H := by
  have hFnF : F ≠ -F := fun he =>
    (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (hP.eq_of_neg_eq hF he.symm)
  have hHnH : H ≠ -H := fun he =>
    (hP.ne_of_dim_ne' (by rw [hH4]; decide)) (hP.eq_of_neg_eq hH he.symm)
  have hFnH : F ≠ -H := by
    intro he
    apply hHnF
    have hh := congrArg (fun S : Set E5 => -S) he
    simpa using hh.symm
  have hnFnH : -F ≠ -H := fun he => hHF (neg_injective he).symm
  have hfour : ({F,-F,H,-H} : Set (Set E5)).ncard = 4 :=
    Set.ncard_eq_four.2 ⟨F,-F,H,-H,hFnF,hHF.symm,hFnH,hHnF.symm,hnFnH,hHnH,rfl⟩
  have hs : ({F,-F,H,-H} : Set (Set E5)) ⊆
      {J | J ∈ faces P ∧ dim J = 4 ∧ cnt P J 0 = 8} := by
    intro J hJ
    rcases hJ with rfl | rfl | rfl | rfl
    · exact ⟨hF,hF4,hF8⟩
    · exact ⟨neg_mem_faces hP.symm hF,by rw [dim_neg,hF4],by rw [hP.cnt_neg,hF8]⟩
    · exact ⟨hH,hH4,hH8⟩
    · exact ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4],by rw [hP.cnt_neg,hH8]⟩
  rw [hP.cnt8_eq_full_ncard] at hc
  have he := Set.eq_of_subset_of_ncard_le hs (by rw [hc,hfour])
    (hP.faces_finite.subset fun J hJ => hJ.1)
  have hm : J ∈ ({F,-F,H,-H} : Set (Set E5)) := he.symm ▸ ⟨hJ,hJ4,hJ8⟩
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm

/-- The cross intersections of a six-vertex full pair have only two
vertices; hence its shared ridge is its only full neighbour. -/
theorem IsCSPolytope5.full_six_partner_unique (hv : fvec P 0 = 16)
    (hc : cnt8 (facetRows P) = 4)
    {F H T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F)
    (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H)
    {J : Set E5} (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hJ8 : cnt P J 0 = 8)
    (hJF : J ≠ F) (hshare : ∃ S ∈ faces P, dim S = 3 ∧ S ⊆ F ∧ S ⊆ J) : J = H := by
  obtain ⟨S,hS,hS3,hSF,hSJ⟩ := hshare
  rcases hP.four_full_exhaust hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hJ hJ4 hJ8 with
    he | he | he | he
  · exact False.elim (hJF he)
  · have hd := hP.disjoint_neg_of_full hF (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (by omega)
    obtain ⟨x,hx⟩ := hS.1
    exact False.elim (Set.disjoint_left.1 hd (hSF hx) (he ▸ hSJ hx))
  · exact he
  · have hFP : F ≠ P := hP.ne_of_dim_ne' (by rw [hF4]; decide)
    have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; decide)
    have hcross := (hP.full_cross_complements hF hFP (by omega) hH hHP (by omega) hTI).1
    have hTF : T ⊆ F := hTI ▸ inter_subset_left
    have hcount : (vset P (F ∩ -H)).ncard = 2 := by
      rw [← hcross,Set.ncard_sdiff (vset_mono' hTF) (hP.vset_finite T),
        ← cnt_eq_vset,← cnt_eq_vset,hF8,hT6]
    have hs : S ⊆ F ∩ -H := subset_inter hSF (he ▸ hSJ)
    have hb := Set.ncard_le_ncard (vset_mono' hs) (hP.vset_finite (F ∩ -H))
    have hlo := hP.four_le_cnt_three hS hS3
    rw [← cnt_eq_vset,hcount] at hb
    omega

end Kalai5
