import Kalai5.Faces.Counting

/-!
# Antipodal facets have the same row

`faceRow P (-F) = faceRow P F` for a centrally symmetric `P`; since `F ↦ -F` has no fixed facet,
every property of rows is shared by an even number of facets.
-/

namespace Kalai5

open Set Pointwise

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.neg_mem_faces_iff {G : Set E5} : -G ∈ faces P ↔ G ∈ faces P :=
  ⟨fun h => by simpa using neg_mem_faces hP.symm h, neg_mem_faces hP.symm⟩

omit hP in
lemma neg_subset_iff {G F : Set E5} : G ⊆ -F ↔ -G ⊆ F := by
  constructor
  · intro h x hx; simpa using h hx
  · intro h x hx; have := h (show -x ∈ -G by simpa using hx); simpa using this

lemma IsCSPolytope5.cnt_neg (F : Set E5) (k : ℕ) : cnt P (-F) k = cnt P F k := by
  have : {G | G ∈ faces P ∧ G ⊆ -F ∧ dim G = k} =
      (fun G : Set E5 => -G) '' {G | G ∈ faces P ∧ G ⊆ F ∧ dim G = k} := by
    ext G; constructor
    · rintro ⟨hG, hGF, hd⟩
      exact ⟨-G, ⟨neg_mem_faces hP.symm hG, neg_subset_iff.1 hGF, by rw [dim_neg]; exact hd⟩,
        neg_neg G⟩
    · rintro ⟨G', ⟨hG', hG'F, hd⟩, rfl⟩
      exact ⟨neg_mem_faces hP.symm hG', Set.neg_subset_neg.2 hG'F, by rw [dim_neg]; exact hd⟩
  rw [cnt, cnt, this, Set.ncard_image_of_injective _ neg_injective]

lemma IsCSPolytope5.incid_neg (F : Set E5) (i j : ℕ) : incid P (-F) i j = incid P F i j := by
  have : {GH : Set E5 × Set E5 | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧ GH.1 ⊆ GH.2 ∧ GH.2 ⊆ -F ∧
      dim GH.1 = i ∧ dim GH.2 = j} =
      (fun GH : Set E5 × Set E5 => (-GH.1, -GH.2)) '' {GH | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧
        GH.1 ⊆ GH.2 ∧ GH.2 ⊆ F ∧ dim GH.1 = i ∧ dim GH.2 = j} := by
    ext ⟨G, H⟩; constructor
    · rintro ⟨hG, hH, hGH, hHF, hdG, hdH⟩
      refine ⟨(-G, -H), ⟨neg_mem_faces hP.symm hG, neg_mem_faces hP.symm hH,
        Set.neg_subset_neg.2 hGH, neg_subset_iff.1 hHF, by rw [dim_neg]; exact hdG,
        by rw [dim_neg]; exact hdH⟩, by simp⟩
    · rintro ⟨⟨G', H'⟩, ⟨hG, hH, hGH, hHF, hdG, hdH⟩, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨neg_mem_faces hP.symm hG, neg_mem_faces hP.symm hH, Set.neg_subset_neg.2 hGH,
        Set.neg_subset_neg.2 hHF, by rw [dim_neg]; exact hdG, by rw [dim_neg]; exact hdH⟩
  have hinj : Function.Injective fun GH : Set E5 × Set E5 => (-GH.1, -GH.2) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ h
    simp only [Prod.mk.injEq, neg_inj] at h
    rw [h.1, h.2]
  rw [incid, incid, this, Set.ncard_image_of_injective _ hinj]

lemma IsCSPolytope5.faceRow_neg (F : Set E5) : faceRow P (-F) = faceRow P F := by
  simp only [faceRow, hP.cnt_neg, hP.incid_neg]

/-- **Every property of rows is shared by an even number of facets.** -/
theorem IsCSPolytope5.facetRows_filter_even (q : Row → Bool) :
    Even ((facetRows P).filter q).length := by
  classical
  set T := (hP.kfaces_finite 4).toFinset
  have hlen : ((facetRows P).filter q).length = (T.filter fun F => q (faceRow P F) = true).card := by
    rw [hP.facetRows_eq, List.filter_map, List.length_map]
    have hnd : (T.toList.filter (q ∘ faceRow P)).Nodup := (Finset.nodup_toList T).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1; ext F; simp [List.mem_filter, Finset.mem_toList]
  rw [hlen]
  refine even_card_of_involution _ (fun F => -F) ?_ (fun F _ => neg_neg F) ?_
  · intro F hF
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hF ⊢
    exact ⟨⟨neg_mem_faces hP.symm hF.1.1, by rw [dim_neg]; exact hF.1.2⟩,
      by rw [hP.faceRow_neg]; exact hF.2⟩
  · intro F hF hFF
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hF
    have := hP.eq_of_neg_eq hF.1.1 hFF
    have h5 := hP.dim_self
    rw [← this, hF.1.2] at h5; omega

end Kalai5
