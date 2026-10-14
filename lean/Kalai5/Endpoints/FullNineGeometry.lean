import Kalai5.Endpoints.AntipodalRidgeCapacity

namespace Kalai5
open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Excluding any specified full facets from the ridge neighbours improves
 the pointwise bound by twice the size of the excluded set. -/
theorem IsCSPolytope5.facet_ridge_capacity_avoiding
    (h16 : fvec P 0 = 16) {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (D : Finset (Set E5))
    (hD : ∀ H ∈ D, H ∈ faces P ∧ dim H = 4 ∧ cnt P H 0 = 8)
    (havoid : ∀ H ∈ D, H ≠ F → ∀ T ∈ faces P, T ⊆ F → dim T = 3 → ¬ T ⊆ H) :
    2 * cnt P F 3 + 2 * D.card ≤ fvec P 4 + cnt8 (facetRows P) := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let Ful := Fs.filter (fun H => cnt P H 0 = 8)
  let NF := Fs.filter (fun H => cnt P H 0 ≠ 8)
  let A := (hP.below_finite F 3).toFinset
  let B := Ful \ D
  let S := NF.filter (fun H => ∃ T ∈ A, T ⊆ H)
  have mFs : ∀ {H}, H ∈ Fs ↔ H ∈ faces P ∧ dim H = 4 := fun {H} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have mA : ∀ {T}, T ∈ A ↔ T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 := fun {T} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have hNFneg : ∀ H ∈ NF, -H ∈ NF := by
    intro H hH
    obtain ⟨hH,hn⟩ := Finset.mem_filter.1 hH
    obtain ⟨hH,hH4⟩ := mFs.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4]⟩,
      by rwa [hP.cnt_neg]⟩
  have hBcard : B.card + D.card = Ful.card := by
    apply Finset.card_sdiff_add_card_eq_card
    intro H hHD
    obtain ⟨hH,hH4,hH8⟩ := hD H hHD
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hH8⟩
  have hAcard : A.card = cnt P F 3 := by
    dsimp only [A]
    rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset]
    rfl
  have hcover : A ⊆ (B ∪ S).image (fun H => F ∩ H) := by
    intro T hTA
    obtain ⟨hT,hTF,hT3⟩ := mA.1 hTA
    obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
    have he := hP.three_face_eq_inter hF h4 hH hH4 hHF.symm hT hT3 hTF hTH
    refine Finset.mem_image.2 ⟨H,?_,he.symm⟩
    by_cases hn : cnt P H 0 = 8
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hn⟩,
        fun hHD => havoid H hHD hHF T hT hTF hT3 hTH⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hn⟩,T,hTA,hTH⟩)
  have hcount : cnt P F 3 ≤ B.card + S.card := by
    have hc := (Finset.card_le_card hcover).trans Finset.card_image_le
    have hu := Finset.card_union_le B S
    rw [hAcard] at hc
    omega
  have hdisj : Disjoint S (S.image (fun H => -H)) := by
    rw [Finset.disjoint_left]
    intro H hHS hHN
    obtain ⟨K,hKS,hKH⟩ := Finset.mem_image.1 hHN
    obtain ⟨hHnf,T,hTA,hTH⟩ := Finset.mem_filter.1 hHS
    obtain ⟨_,U,hUA,hUK⟩ := Finset.mem_filter.1 hKS
    obtain ⟨hHfs,hH8⟩ := Finset.mem_filter.1 hHnf
    obtain ⟨hH,hH4⟩ := mFs.1 hHfs
    obtain ⟨hT,hTF,hT3⟩ := mA.1 hTA
    obtain ⟨hU,hUF,hU3⟩ := mA.1 hUA
    have hnUH : -U ⊆ H := by
      rw [← hKH]
      exact Set.neg_subset_neg.2 hUK
    have hd : Disjoint T (-U) :=
      Set.disjoint_of_subset hTF (Set.neg_subset_neg.2 hUF) (hP.facet_disjoint_neg hF h4)
    have hlo := hP.eight_le_cnt_of_disjoint hH hT hT3
      (neg_mem_faces hP.symm hU) (by rw [dim_neg,hU3]) hTH hnUH hd
    have hneP : H ≠ P := by
      intro he
      have hdim := hP.dim_self
      rw [← he,hH4] at hdim
      omega
    have hhi := hP.two_mul_cnt_le hH hneP
    omega
  have hsub : S ∪ S.image (fun H => -H) ⊆ NF := by
    intro H hH
    rcases Finset.mem_union.1 hH with hs | hs
    · exact (Finset.mem_filter.1 hs).1
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.1 hs
      exact hNFneg K (Finset.mem_filter.1 hK).1
  have hsmall := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,Finset.card_image_of_injective _ neg_injective] at hsmall
  have hpartition : Ful.card + NF.card = Fs.card :=
    Finset.card_filter_add_card_filter_not (s := Fs) (p := fun H => cnt P H 0 = 8)
  have hFs : Fs.card = fvec P 4 := by
    dsimp only [Fs]
    rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset]
    rfl
  have hFul : Ful.card = cnt8 (facetRows P) := by
    rw [cnt8,length_filter_eq_sum,hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0)]
    simp only [Ful,Fs,Finset.card_filter]
    rfl
  omega

/-- A full facet with nine ridges cannot share a ridge of at least five
vertices with another full facet when there are only four full facets. -/
theorem IsCSPolytope5.full_nine_large_ridge_partner_nonfull
    (h16 : fvec P 0 = 16) (h18 : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (h8 : cnt P F 0 = 8) (hr : cnt P F 3 = 9)
    {T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hT5 : 5 ≤ cnt P T 0)
    {H : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4) (hHF : H ≠ F) (hTH : T ⊆ H) :
    cnt P H 0 ≠ 8 := by
  intro hH8
  have hFn : F ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hF.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF h4) hx (he ▸ hx)
  have hHnF : H ≠ -F := by
    intro he
    obtain ⟨x,hx⟩ := hT.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF h4) (hTF hx) (he ▸ hTH hx)
  have hnHF : -H ≠ F := by
    intro he
    apply hHnF
    rw [← he,neg_neg]
  have hnHnF : -H ≠ -F := fun he => hHF (neg_injective he)
  have hcard : ({-H,F,-F} : Finset (Set E5)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto),
      Finset.card_pair hFn]
  have hc := hP.facet_ridge_capacity_avoiding h16 hF h4 {-H,F,-F}
    (fun K hK => ?_) (fun K hK hKF U hU hUF hU3 hUK => ?_)
  · rw [hcard] at hc
    omega
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4],by rw [hP.cnt_neg,hH8]⟩
    · exact ⟨hF,h4,h8⟩
    · exact ⟨neg_mem_faces hP.symm hF,by rw [dim_neg,h4],by rw [hP.cnt_neg,h8]⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · have hd := Set.disjoint_of_subset hTH hUK (hP.facet_disjoint_neg hH hH4)
      have hlo := hP.four_le_cnt_three hU hU3
      have hsum := hP.cnt_zero_add_le_of_disjoint hTF hUF hd
      omega
    · exact hKF rfl
    · obtain ⟨x,hx⟩ := hU.1
      exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF h4) (hUF hx) (hUK hx)

end Kalai5
