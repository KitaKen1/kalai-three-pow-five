import Kalai5.Endpoints.FullNineGeometry
import Kalai5.Endpoints.WeightR0

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Saturating the nine-ridge bound forces adjacency to every other full
facet except the antipode. -/
theorem IsCSPolytope5.full_nine_meets_other_full
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    {F H : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hF8 : cnt P F 0 = 8) (hr : cnt P F 3 = 9)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) :
    ∃ T ∈ faces P, T ⊆ F ∧ dim T = 3 ∧ T ⊆ H := by
  by_contra hn
  have hFn : F ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hF.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4) hx (he ▸ hx)
  have hcard : ({H,F,-F} : Finset (Set E5)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto),
      Finset.card_pair hFn]
  have hb := hP.facet_ridge_capacity_avoiding hv hF hF4 {H,F,-F}
    (fun K hK => ?_) (fun K hK hKF T hT hTF hT3 hTK => ?_)
  · rw [hcard] at hb
    omega
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact ⟨hH,hH4,hH8⟩
    · exact ⟨hF,hF4,hF8⟩
    · exact ⟨neg_mem_faces hP.symm hF,by rw [dim_neg,hF4],by rw [hP.cnt_neg,hF8]⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hn ⟨T,hT,hTF,hT3,hTK⟩
    · exact hKF rfl
    · obtain ⟨x,hx⟩ := hT.1
      exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4) (hTF hx) (hTK hx)

/-- Every full neighbour of a nine-ridge facet needs two distinct
four-vertex ridges, one facing each sign of that facet. -/
theorem IsCSPolytope5.full_nine_other_full_two_tetra
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    {F H : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hF8 : cnt P F 0 = 8) (hr : cnt P F 3 = 9)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hH8 : cnt P H 0 = 8)
    (hHF : H ≠ F) (hHnF : H ≠ -F) : 2 ≤ tcnt P H (4,6,4) := by
  obtain ⟨T,hT,hTF,hT3,hTH⟩ := hP.full_nine_meets_other_full hv hh hc hF hF4 hF8 hr hH hH4 hH8 hHF hHnF
  have hnF := neg_mem_faces hP.symm hF
  have hnF4 : dim (-F) = 4 := by rw [dim_neg,hF4]
  have hnF8 : cnt P (-F) 0 = 8 := by rw [hP.cnt_neg,hF8]
  have hnr : cnt P (-F) 3 = 9 := by rw [hP.cnt_neg,hr]
  obtain ⟨U,hU,hUnF,hU3,hUH⟩ := hP.full_nine_meets_other_full hv hh hc hnF hnF4 hnF8 hnr hH hH4 hH8 hHnF (by simpa using hHF)
  have tetra : ∀ {K X : Set E5}, X ∈ faces P → dim X = 4 → cnt P X 0 = 8 → cnt P X 3 = 9 →
      H ≠ X → K ∈ faces P → K ⊆ X → dim K = 3 → K ⊆ H → tri3 P K = (4,6,4) := by
    intro K X hX hX4 hX8 hX9 hHX hK hKX hK3 hKH
    have hnot := hP.full_nine_large_ridge_partner_nonfull hv hh hc hX hX4 hX8 hX9 hK hKX hK3
    have hn : cnt P K 0 ≤ 4 := by
      by_contra hn
      exact hnot (by omega) hH hH4 hHX hKH hH8
    have hm := hP.tri3_mem_fv8 hK hK3 (by omega)
    simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with he | he | he | he | he | he | he | he | he | he | he | he
    · exact he
    all_goals have he' := congrArg Prod.fst he; change cnt P K 0 = _ at he'; omega
  have ht := tetra hF hF4 hF8 hr hHF hT hTF hT3 hTH
  have hu := tetra hnF hnF4 hnF8 hnr hHnF hU hUnF hU3 hUH
  have hne : T ≠ U := by
    intro he
    obtain ⟨x,hx⟩ := hT.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4) (hTF hx) (hUnF (he ▸ hx))
  have hs : ({T,U} : Set (Set E5)) ⊆ {K | K ∈ faces P ∧ K ⊆ H ∧ dim K = 3 ∧ tri3 P K = (4,6,4)} := by
    intro K hK
    rcases (show K = T ∨ K = U by simpa using hK) with rfl | rfl
    · exact ⟨hT,hTH,hT3,ht⟩
    · exact ⟨hU,hUH,hU3,hu⟩
  have hb := Set.ncard_le_ncard hs (hP.faces_finite.subset fun K hK => hK.1)
  rw [Set.ncard_pair hne] at hb
  exact hb

end Kalai5
