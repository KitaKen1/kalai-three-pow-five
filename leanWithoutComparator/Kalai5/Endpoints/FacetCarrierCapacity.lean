import Kalai5.Endpoints.G2S4R35

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Carrier facets may be selected by their actual geometric weight.
Only closure under the antipodal map is needed for the pair capacity. -/
theorem IsCSPolytope5.ridge_facet_predicate_capacity
    (carrier : Set E5 → Prop) [DecidablePred carrier]
    (hneg : ∀ H ∈ faces P, dim H = 4 → carrier H → carrier (-H))
    {F : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hFC : carrier F) (A : Finset (Set E5))
    (hA : ∀ T ∈ A, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3)
    (hwide : ∀ T ∈ A, ∀ U ∈ A, cnt P F 0 < cnt P T 0 + cnt P U 0)
    (hcar : ∀ T ∈ A, ∀ H ∈ faces P, dim H = 4 → T ⊆ H → carrier H) :
    2 * A.card + 2 ≤ ((hP.kfaces_finite 4).toFinset.filter carrier).card := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let C := Fs.filter (fun H => carrier H)
  let S := Fs.filter (fun H => H ≠ F ∧ ∃ T ∈ A, T ⊆ H)
  have mFs : ∀ {H}, H ∈ Fs ↔ H ∈ faces P ∧ dim H = 4 := fun {H} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have mS : ∀ {H}, H ∈ S ↔ H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ ∃ T ∈ A, T ⊆ H := by
    intro H
    simp only [S,Finset.mem_filter,mFs]
    tauto
  have hSC : ∀ H ∈ S, H ∈ C := by
    intro H hH
    obtain ⟨hH,hH4,_,T,hTA,hTH⟩ := mS.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hcar T hTA H hH hH4 hTH⟩
  have hCn : ∀ H ∈ C, -H ∈ C := by
    intro H hH
    obtain ⟨hH,hHC⟩ := Finset.mem_filter.1 hH
    obtain ⟨hH,hH4⟩ := mFs.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4]⟩,
      hneg H hH hH4 hHC⟩
  have hcard : A.card ≤ S.card := by
    have hs : A ⊆ S.image (fun H => F ∩ H) := by
      intro T hTA
      obtain ⟨hT,hTF,hT3⟩ := hA T hTA
      obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
      refine Finset.mem_image.2 ⟨H,mS.2 ⟨hH,hH4,hHF,T,hTA,hTH⟩,?_⟩
      exact (hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hT hT3 hTF hTH).symm
    exact (Finset.card_le_card hs).trans Finset.card_image_le
  have hdisj : Disjoint S (S.image (fun H => -H)) := by
    rw [Finset.disjoint_left]
    intro H hHS hHN
    obtain ⟨K,hKS,hKH⟩ := Finset.mem_image.1 hHN
    obtain ⟨hH,hH4,_,T,hTA,hTH⟩ := mS.1 hHS
    obtain ⟨_,_,_,U,hUA,hUK⟩ := mS.1 hKS
    have hUnH : U ⊆ -H := by rw [← hKH,neg_neg]; exact hUK
    have hd := Set.disjoint_of_subset hTH hUnH (hP.facet_disjoint_neg hH hH4)
    have hc := hP.cnt_zero_add_le_of_disjoint (hA T hTA).2.1 (hA U hUA).2.1 hd
    exact (not_lt_of_ge hc) (hwide T hTA U hUA)
  have hnotF : F ∉ S := fun hm => (mS.1 hm).2.2.1 rfl
  have hnotN : -F ∉ S := by
    intro hm
    obtain ⟨_,_,_,T,hTA,hTN⟩ := mS.1 hm
    obtain ⟨x,hx⟩ := (hA T hTA).1.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4)
      ((hA T hTA).2.1 hx) (hTN hx)
  have hsub : S ∪ S.image (fun H => -H) ⊆ (C.erase F).erase (-F) := by
    intro H hH
    rcases Finset.mem_union.1 hH with hs | hs
    · exact Finset.mem_erase.2 ⟨fun he => hnotN (he ▸ hs),
        Finset.mem_erase.2 ⟨fun he => hnotF (he ▸ hs),hSC H hs⟩⟩
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.1 hs
      exact Finset.mem_erase.2 ⟨fun he => hnotF ((neg_injective he) ▸ hK),
        Finset.mem_erase.2 ⟨fun he => hnotN ((neg_eq_iff_eq_neg.1 he) ▸ hK),hCn K (hSC K hK)⟩⟩
  have hFC' : F ∈ C := Finset.mem_filter.2 ⟨mFs.2 ⟨hF,hF4⟩,hFC⟩
  have hne : -F ≠ F := fun he =>
    (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (hP.eq_of_neg_eq hF he)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,Finset.card_image_of_injective _ neg_injective,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne,hCn F hFC'⟩),
    Finset.card_erase_of_mem hFC'] at hc
  have ht : 2 ≤ C.card := by
    have hs : ({F,-F} : Finset (Set E5)) ⊆ C := by
      intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH
      · exact hFC'
      · exact Finset.mem_singleton.1 hH ▸ hCn F hFC'
    have hh := Finset.card_le_card hs
    rwa [Finset.card_pair hne.symm] at hh
  change 2 * A.card + 2 ≤ C.card
  omega

end Kalai5
