import Kalai5.Endpoints.FullRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- With four full eight-ridge facets, each having at most one full neighbour,
eighteen facets force every non-full facet to meet exactly two full facets. -/
theorem IsCSPolytope5.full_ridge_saturation_four
    (h16 : fvec P 0 = 16) (h18 : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    (hr : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 → cnt P F 3 = 8)
    (hone : ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
      ∃ H, ∀ J ∈ faces P, dim J = 4 → cnt P J 0 = 8 → J ≠ F →
        (∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ J) → J = H)
    {X : Set E5} (hX : X ∈ faces P) (hX4 : dim X = 4) (hX8 : cnt P X 0 ≠ 8) :
    {F | F ∈ faces P ∧ dim F = 4 ∧ cnt P F 0 = 8 ∧
      ∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ X}.ncard = 2 := by
  set Fs := (hP.kfaces_finite 4).toFinset with hFs
  set Ts := (hP.kfaces_finite 3).toFinset with hTs
  set Ful := Fs.filter (fun F => cnt P F 0 = 8) with hFul
  set NF := Fs.filter (fun F => ¬ cnt P F 0 = 8) with hNF
  have mFs : ∀ {F}, F ∈ Fs ↔ F ∈ faces P ∧ dim F = 4 := fun {F} => by
    rw [hFs,Set.Finite.mem_toFinset]; rfl
  have mTs : ∀ {T}, T ∈ Ts ↔ T ∈ faces P ∧ dim T = 3 := fun {T} => by
    rw [hTs,Set.Finite.mem_toFinset]; rfl
  have mFul : ∀ {F}, F ∈ Ful ↔ (F ∈ faces P ∧ dim F = 4) ∧ cnt P F 0 = 8 := fun {F} => by
    rw [hFul,Finset.mem_filter,mFs]
  have fne : ∀ {F}, F ∈ faces P → dim F = 4 → F ≠ P := fun _ hd he => by
    have := hP.dim_self; rw [← he,hd] at this; omega
  have fdisj : ∀ {F}, F ∈ Ful → Disjoint F (-F) := fun hF => by
    obtain ⟨⟨hF,hd⟩,h8⟩ := mFul.1 hF
    exact hP.disjoint_neg_of_full hF (fne hF hd) (by omega)
  have fneg : ∀ {F}, F ∈ Ful → -F ∈ Ful := fun hF => by
    obtain ⟨⟨hF,hd⟩,h8⟩ := mFul.1 hF
    exact mFul.2 ⟨⟨neg_mem_faces hP.symm hF,by rw [dim_neg,hd]⟩,by rw [hP.cnt_neg,h8]⟩
  have cle : ∀ {J}, J ∈ Fs → cnt P J 0 ≤ 8 := fun hJ => by
    obtain ⟨hJ,hd⟩ := mFs.1 hJ
    have := hP.two_mul_cnt_le hJ (fne hJ hd)
    omega
  have hFc : Ful.card = 4 := by
    have hc : cnt8 (facetRows P) = Ful.card := by
      rw [cnt8,length_filter_eq_sum,hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0),
        hFul,Finset.card_filter]
      rfl
    omega
  have hNc : NF.card = 14 := by
    have hf : Fs.card = 18 := by
      rw [hFs,← Set.ncard_coe_finset,Set.Finite.coe_toFinset]
      exact h18
    have := Finset.card_filter_add_card_filter_not (s := Fs) (p := fun F => cnt P F 0 = 8)
    rw [← hFul,← hNF] at this
    omega
  set rel : Set E5 → Set E5 → Prop := fun F J => ∃ T ∈ Ts, T ⊆ F ∧ T ⊆ J with hrel
  have step1 : ∀ F ∈ Ful, 8 ≤ 1 + (NF.filter (rel F)).card := by
    intro F hF
    obtain ⟨⟨hFf,hF4⟩,hF8⟩ := mFul.1 hF
    obtain ⟨H,hH⟩ := hone F hFf hF4 hF8
    set B := (NF.filter (rel F)).image (fun J => F ∩ J) with hB
    have hs : Ts.filter (· ⊆ F) ⊆ insert (F ∩ H) B := by
      intro T hT
      rw [Finset.mem_filter,mTs] at hT
      obtain ⟨⟨hT,hT3⟩,hTF⟩ := hT
      obtain ⟨J,hJ,hJ4,hJF,hTJ⟩ := hP.exists_other_facet hT hT3 hTF
      have he := hP.three_face_eq_inter hFf hF4 hJ hJ4 hJF.symm hT hT3 hTF hTJ
      by_cases hJ8 : cnt P J 0 = 8
      · have hJH := hH J hJ hJ4 hJ8 hJF ⟨T,hT,hT3,hTF,hTJ⟩
        rw [he,hJH]
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.2 ⟨J,Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨mFs.2 ⟨hJ,hJ4⟩,hJ8⟩,
            ⟨T,mTs.2 ⟨hT,hT3⟩,hTF,hTJ⟩⟩,he.symm⟩
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_insert_le (F ∩ H) B
    have h3 : B.card ≤ (NF.filter (rel F)).card := Finset.card_image_le
    have h4 : (Ts.filter (· ⊆ F)).card = 8 := by
      rw [hTs,← hP.cnt_three_eq F]
      exact hr F hFf hF4 hF8
    omega
  have step2 : ∀ J ∈ NF, (Ful.filter (fun F => rel F J)).card ≤ 2 := by
    intro J hJ
    rw [hNF,Finset.mem_filter] at hJ
    obtain ⟨hJfs,hJ8⟩ := hJ
    have hJf := (mFs.1 hJfs).1
    set S := Ful.filter (fun F => rel F J) with hS
    have hd : Disjoint S (S.image (fun F => -F)) := by
      rw [Finset.disjoint_left]
      intro F hF hF'
      obtain ⟨G,hG,hGF⟩ := Finset.mem_image.1 hF'
      rw [hS,Finset.mem_filter] at hF hG
      obtain ⟨hFful,T,hT,hTF,hTJ⟩ := hF
      obtain ⟨_,U,hU,hUG,hUJ⟩ := hG
      rw [mTs] at hT hU
      have hUnF : U ⊆ -F := by rw [← hGF,neg_neg]; exact hUG
      have hdisj := Set.disjoint_of_subset hTF hUnF (fdisj hFful)
      have := hP.eight_le_cnt_of_disjoint hJf hT.1 hT.2 hU.1 hU.2 hTJ hUJ hdisj
      have := cle hJfs
      omega
    have hs : S ∪ S.image (fun F => -F) ⊆ Ful := by
      intro F hF
      rcases Finset.mem_union.1 hF with hF | hF
      · exact (Finset.mem_filter.1 hF).1
      · obtain ⟨G,hG,rfl⟩ := Finset.mem_image.1 hF
        exact fneg (Finset.mem_filter.1 hG).1
    have hc := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ neg_injective,hFc] at hc
    omega
  have hsum1 := Finset.sum_le_sum step1
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_const,smul_eq_mul,smul_eq_mul,hFc] at hsum1
  have hswap : ∑ F ∈ Ful, (NF.filter (rel F)).card = ∑ J ∈ NF, (Ful.filter (fun F => rel F J)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap] at hsum1
  have hXNF : X ∈ NF := Finset.mem_filter.2 ⟨mFs.2 ⟨hX,hX4⟩,hX8⟩
  have hdeg : (Ful.filter (fun F => rel F X)).card = 2 := by
    have hlo := step2 X hXNF
    by_contra hne
    have hstrict := Finset.sum_lt_sum step2 ⟨X,hXNF,by omega⟩
    rw [Finset.sum_const,smul_eq_mul,hNc] at hstrict
    omega
  have he : {F | F ∈ faces P ∧ dim F = 4 ∧ cnt P F 0 = 8 ∧
      ∃ T ∈ faces P, dim T = 3 ∧ T ⊆ F ∧ T ⊆ X} =
      (↑(Ful.filter (fun F => rel F X)) : Set (Set E5)) := by
    ext F
    simp only [Finset.mem_coe,Finset.mem_filter,mFul,hrel]
    constructor
    · rintro ⟨hF,hF4,hF8,T,hT,hT3,hTF,hTX⟩
      exact ⟨⟨⟨hF,hF4⟩,hF8⟩,T,mTs.2 ⟨hT,hT3⟩,hTF,hTX⟩
    · rintro ⟨⟨⟨hF,hF4⟩,hF8⟩,T,hT,hTF,hTX⟩
      exact ⟨hF,hF4,hF8,T,(mTs.1 hT).1,(mTs.1 hT).2,hTF,hTX⟩
  rw [he,Set.ncard_coe_finset,hdeg]

end Kalai5
