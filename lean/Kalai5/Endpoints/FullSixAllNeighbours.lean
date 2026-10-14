import Kalai5.Endpoints.FullPairExhaust

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- With two full pairs, a single shared six-vertex ridge fixes the
unique full neighbour of all four full facets. -/
theorem IsCSPolytope5.full_six_all_partner_unique
    (hv : fvec P 0 = 16) (hc : cnt8 (facetRows P) = 4)
    {F H T : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) (hT6 : cnt P T 0 = 6) (hTI : T = F ∩ H) :
    ∀ K ∈ faces P, dim K = 4 → cnt P K 0 = 8 →
      ∃ L, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ K →
        (∃ U ∈ faces P, dim U = 3 ∧ U ⊆ K ∧ U ⊆ J) → J = L := by
  have hFnH : F ≠ -H := by intro he; apply hHnF; rw [he,neg_neg]
  have hnT : -T = -F ∩ -H := by rw [hTI]; ext x; simp
  have hnF := neg_mem_faces hP.symm hF
  have hnH := neg_mem_faces hP.symm hH
  have hnF4 : dim (-F) = 4 := by rw [dim_neg,hF4]
  have hnH4 : dim (-H) = 4 := by rw [dim_neg,hH4]
  have hnF8 : cnt P (-F) 0 = 8 := by rw [hP.cnt_neg,hF8]
  have hnH8 : cnt P (-H) 0 = 8 := by rw [hP.cnt_neg,hH8]
  have hnT6 : cnt P (-T) 0 = 6 := by rw [hP.cnt_neg,hT6]
  intro K hK hK4 hK8
  rcases hP.four_full_exhaust hc hF hF4 hF8 hH hH4 hH8 hHF hHnF hK hK4 hK8 with rfl | rfl | rfl | rfl
  · exact ⟨H,fun J hJ hJ4 hJ8 hJF hs => hP.full_six_partner_unique hv hc hF hF4 hF8 hH hH4 hH8
      hHF hHnF hT6 hTI hJ hJ4 hJ8 hJF hs⟩
  · exact ⟨-H,fun J hJ hJ4 hJ8 hJF hs => hP.full_six_partner_unique hv hc hnF hnF4 hnF8 hnH hnH4 hnH8
      (fun he => hHF (neg_injective he)) (by simpa only [neg_neg] using hFnH.symm)
      hnT6 hnT hJ hJ4 hJ8 hJF hs⟩
  · exact ⟨F,fun J hJ hJ4 hJ8 hJF hs => hP.full_six_partner_unique hv hc hH hH4 hH8 hF hF4 hF8
      hHF.symm hFnH hT6 (by rw [hTI,inter_comm]) hJ hJ4 hJ8 hJF hs⟩
  · exact ⟨-F,fun J hJ hJ4 hJ8 hJF hs => hP.full_six_partner_unique hv hc hnH hnH4 hnH8 hnF hnF4 hnF8
      (fun he => hHF (neg_injective he).symm) (by simpa only [neg_neg] using hHnF.symm)
      hnT6 (by rw [hnT,inter_comm]) hJ hJ4 hJ8 hJF hs⟩

end Kalai5
