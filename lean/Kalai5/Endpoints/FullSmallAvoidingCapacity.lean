import Kalai5.Endpoints.AntipodalRidgeCapacity

namespace Kalai5
open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Each missed small facet consumes one further slot in the antipodal
ridge-neighbour capacity, in addition to excluded full facets. -/
theorem IsCSPolytope5.facet_ridge_capacity_avoiding_small
    (h16 : fvec P 0 = 16) {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (D : Finset (Set E5))
    (hD : ∀ H ∈ D, H ∈ faces P ∧ dim H = 4 ∧ cnt P H 0 = 8)
    (havoid : ∀ H ∈ D, H ≠ F → ∀ T ∈ faces P, T ⊆ F → dim T = 3 → ¬ T ⊆ H)
    (E : Finset (Set E5))
    (hE : ∀ H ∈ E, H ∈ faces P ∧ dim H = 4 ∧ cnt P H 0 ≠ 8)
    (hmiss : ∀ H ∈ E, ∀ T ∈ faces P, T ⊆ F → dim T = 3 → (¬ T ⊆ H) ∧ (¬ T ⊆ -H)) :
    2 * cnt P F 3 + 2 * D.card + E.card ≤ fvec P 4 + cnt8 (facetRows P) := by
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
  have hEsub : E ⊆ NF := by
    intro H hHE
    obtain ⟨hH,hH4,hH8⟩ := hE H hHE
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hH8⟩
  have hEd : Disjoint (S ∪ S.image (fun H => -H)) E := by
    rw [Finset.disjoint_left]
    intro H hHS hHE
    rcases Finset.mem_union.1 hHS with hs | hs
    · obtain ⟨_,T,hTA,hTH⟩ := Finset.mem_filter.1 hs
      obtain ⟨hT,hTF,hT3⟩ := mA.1 hTA
      exact (hmiss H hHE T hT hTF hT3).1 hTH
    · obtain ⟨K,hKS,hKH⟩ := Finset.mem_image.1 hs
      obtain ⟨_,T,hTA,hTK⟩ := Finset.mem_filter.1 hKS
      obtain ⟨hT,hTF,hT3⟩ := mA.1 hTA
      exact (hmiss H hHE T hT hTF hT3).2 (by rw [← hKH,neg_neg]; exact hTK)
  have hsmall := Finset.card_le_card (Finset.union_subset hsub hEsub)
  rw [Finset.card_union_of_disjoint hEd,Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ neg_injective] at hsmall
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

end Kalai5
