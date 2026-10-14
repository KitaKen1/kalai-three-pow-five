import Kalai5.Endpoints.Z20.QuadLink
import Kalai5.Endpoints.FullRidge

/-!
# The (5,5)-quadrilateral inequality: local core

For a quadrilateral 2-face `Q` of a cs 5-polytope with sixteen vertices and a facet `H ⊇ Q`, the
two 3-faces of `H` through `Q` are `R, S` with `R ∩ S = Q`, so `|R| + |S| ≤ |H| + 4 ≤ 12`.

* **Full cover** (`IsCSPolytope5.four_le_up_of_cover`): if `H` is full and `R ∪ S` contains all
  vertices of `H`, then `Q` lies in at least four facets.  Otherwise the other facets `G_R ⊇ R`,
  `G_S ⊇ S` share the third 3-face `T` through `Q`; a vertex `w ∈ T` outside `H` has `-w ∈ H`, hence
  `-w ∈ R ⊆ G_R` or `-w ∈ S ⊆ G_S`, and a proper face contains no antipodal pair; so `T ⊆ H`,
  but the only 3-faces of `H` through `Q` are `R` and `S`.
* Consequently (`IsCSPolytope5.le_one_big`) at most one of `R, S` has six or more vertices when
  `Q` lies in exactly three facets.
-/

namespace Kalai5

open Set

open scoped Classical

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Faces with inclusion and equal dimension coincide. -/
lemma IsCSPolytope5.eq_of_subset_of_dim_le {A B : Set E5} (hA : A ∈ faces P) (hB : B ∈ faces P)
    (hAB : A ⊆ B) (hd : dim B ≤ dim A) : A = B := by
  by_contra hne
  have hAB' : A ∈ faces B := mem_faces_of_subset (face_subset hB) hA hAB
  have := dim_lt_of_mem_faces_ne hAB' hne
  omega

/-- Dimension is monotone on faces. -/
lemma IsCSPolytope5.dim_le_of_subset {A B : Set E5} (hA : A ∈ faces P) (hB : B ∈ faces P)
    (hAB : A ⊆ B) : dim A ≤ dim B := by
  by_cases h : A = B
  · rw [h]
  · have hAB' : A ∈ faces B := mem_faces_of_subset (face_subset hB) hA hAB
    exact (dim_lt_of_mem_faces_ne hAB' h).le

/-- Two distinct 3-faces through a 2-face `Q` meet exactly in `Q`. -/
lemma IsCSPolytope5.inter_three_eq {Q R S : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2)
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hS : S ∈ faces P) (hS3 : dim S = 3) (hRS : R ≠ S)
    (hQR : Q ⊆ R) (hQS : Q ⊆ S) : R ∩ S = Q := by
  have hI : R ∩ S ∈ faces P :=
    inter_mem_faces_of_nonempty hR hS (hQ.1.mono (subset_inter hQR hQS))
  have hIR : R ∩ S ∈ faces R := mem_faces_of_subset (face_subset hR) hI inter_subset_left
  have hne : R ∩ S ≠ R := by
    intro h
    have hRS' : R ⊆ S := by rw [← h]; exact inter_subset_right
    exact hRS (hP.eq_of_subset_of_dim_le hR hS hRS' (by omega))
  have hlt := dim_lt_of_mem_faces_ne hIR hne
  exact (hP.eq_of_subset_of_dim_le hQ hI (subset_inter hQR hQS) (by omega)).symm

/-- A face of dimension other than five is proper. -/
lemma IsCSPolytope5.ne_of_dim_ne' {G : Set E5} (hG : dim G ≠ 5) : G ≠ P := by
  rintro rfl
  exact hG hP.dim_self

/-- The negative of a vertex is a vertex. -/
lemma IsCSPolytope5.neg_extreme {z : E5} (hz : z ∈ P.extremePoints ℝ) :
    -z ∈ P.extremePoints ℝ := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hz' := hz
  rw [hV] at hz'
  have h1 := singleton_mem_faces_of_extreme hz'
  rw [← hV] at h1
  have h2 := neg_mem_faces hP.symm h1
  rw [Set.neg_singleton] at h2
  exact isExtreme_singleton.1 h2.2.isExtreme

/-- **Full cover**: if the two 3-faces `R, S` through a 2-face `Q` of a full facet `H` contain all
vertices of `H`, then `Q` lies in at least four facets. -/
theorem IsCSPolytope5.four_le_up_of_cover {W : Finset E5} (hPW : P = convexHull ℝ (W : Set E5))
    (hcp : ConvPos W) {H Q R S : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4)
    (hfull : 2 * cnt P H 0 = fvec P 0) (hQ : Q ∈ faces P) (h2 : dim Q = 2)
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hS : S ∈ faces P) (hS3 : dim S = 3) (hRS : R ≠ S)
    (hQR : Q ⊆ R) (hQS : Q ⊆ S) (hRH : R ⊆ H) (hSH : S ⊆ H)
    (hcov : ∀ w ∈ W, w ∈ H → w ∈ R ∨ w ∈ S) :
    4 ≤ {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard := by
  by_contra hlt
  push Not at hlt
  have h3 := hP.three_le_up hQ h2
  have hℓ : {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard = 3 := by omega
  have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; norm_num)
  obtain ⟨u, hu1, hHu, hupm⟩ := hP.exists_full_normal hH hHP hfull
  -- the other facets through `R` and `S`
  obtain ⟨GR, hGR, hGR4, hGRH, hRGR⟩ := hP.exists_other_facet hR hR3 hRH
  obtain ⟨GS, hGS, hGS4, hGSH, hSGS⟩ := hP.exists_other_facet hS hS3 hSH
  have hGRP : GR ≠ P := hP.ne_of_dim_ne' (by rw [hGR4]; norm_num)
  have hGSP : GS ≠ P := hP.ne_of_dim_ne' (by rw [hGS4]; norm_num)
  -- `H` is the convex hull of its vertices
  have hHconv : H = convexHull ℝ ((W.filter (· ∈ H) : Finset E5) : Set E5) := by
    rw [hPW] at hH
    exact face_eq_convexHull_filter hH
  have hGRS : GR ≠ GS := by
    intro he
    apply hGRH
    -- `H ⊆ GR`: every vertex of `H` lies in `R ∪ S ⊆ GR`
    have hsub : H ⊆ GR := by
      rw [hHconv]
      refine convexHull_min (fun w hw => ?_) (face_convex hP.convex hGR)
      rw [Finset.coe_filter] at hw
      rcases hcov w hw.1 hw.2 with h | h
      · exact hRGR h
      · rw [he]; exact hSGS h
    exact (hP.eq_of_subset_of_dim_le hH hGR hsub (by omega)).symm
  -- the facets through `Q` are `H, GR, GS`
  have hset : {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4} = {H, GR, GS} := by
    have hsub : ({H, GR, GS} : Set (Set E5)) ⊆ {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4} := by
      intro F hF
      rcases hF with rfl | rfl | rfl
      · exact ⟨hH, hQR.trans hRH, hH4⟩
      · exact ⟨hGR, hQR.trans hRGR, hGR4⟩
      · exact ⟨hGS, hQS.trans hSGS, hGS4⟩
    have hcard : ({H, GR, GS} : Set (Set E5)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
          rintro (h | h)
          · exact hGRH h.symm
          · exact hGSH h.symm),
        Set.ncard_pair hGRS]
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hℓ, hcard])
      (hP.above_finite Q 4)).symm
  -- the third 3-face through `Q`
  have hT3 : {T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3}.ncard = 3 := by
    rw [hP.up_three_eq_up_four hQ h2, hℓ]
  obtain ⟨T, ⟨hT, hQT, hTd⟩, hTR, hTS⟩ : ∃ T ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3},
      T ≠ R ∧ T ≠ S := by
    by_contra hno
    push Not at hno
    have hsub : {T | T ∈ faces P ∧ Q ⊆ T ∧ dim T = 3} ⊆ {R, S} := by
      intro T hT
      by_cases h : T = R
      · exact Or.inl h
      · exact Or.inr (hno T hT h)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hRS, hT3] at this
    omega
  -- `T` is not inside `H`: the 3-faces of `H` through `Q` are `R` and `S`
  have hTH : ¬ T ⊆ H := by
    intro hTH
    have hcnt := hP.card_three_through hH hH4 hQ (hQR.trans hRH) h2
    have hsub : ({R, S, T} : Finset (Set E5)) ⊆
        (hP.below_finite H 3).toFinset.filter fun T' => Q ⊆ T' := by
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      rcases hX with rfl | rfl | rfl
      · exact ⟨⟨hR, hRH, hR3⟩, hQR⟩
      · exact ⟨⟨hS, hSH, hS3⟩, hQS⟩
      · exact ⟨⟨hT, hTH, hTd⟩, hQT⟩
    have := Finset.card_le_card hsub
    rw [hcnt, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact hRS h
        · exact hTR h.symm),
      Finset.card_pair (Ne.symm hTS)] at this
    omega
  -- `T` lies in two facets through `Q`, not `H`: so in `GR` and `GS`
  have hTfac := hP.ridge_two hT hTd
  have hTsub : {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4} ⊆ {GR, GS} := by
    intro F hF
    have hF' : F ∈ ({H, GR, GS} : Set (Set E5)) := by
      rw [← hset]; exact ⟨hF.1, hQT.trans hF.2.1, hF.2.2⟩
    rcases hF' with rfl | h
    · exact absurd hF.2.1 hTH
    · exact h
  have hTeq : {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4} = {GR, GS} :=
    Set.eq_of_subset_of_ncard_le hTsub (by rw [Set.ncard_pair hGRS, hTfac]) (Set.toFinite _)
  have hTGR : T ⊆ GR := by
    have : GR ∈ {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4} := by rw [hTeq]; exact Or.inl rfl
    exact this.2.1
  have hTGS : T ⊆ GS := by
    have : GS ∈ {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4} := by rw [hTeq]; exact Or.inr rfl
    exact this.2.1
  -- every vertex of `T` lies in `H`
  apply hTH
  have hTconv : T = convexHull ℝ ((W.filter (· ∈ T) : Finset E5) : Set E5) := by
    rw [hPW] at hT
    exact face_eq_convexHull_filter hT
  rw [hTconv]
  refine convexHull_min (fun w hw => ?_) (face_convex hP.convex hH)
  rw [Finset.coe_filter] at hw
  obtain ⟨hwW, hwT⟩ := hw
  have hwP : w ∈ P := face_subset hT hwT
  have hwext : w ∈ P.extremePoints ℝ := by
    rw [hPW]; exact hcp w hwW
  by_contra hwH
  have hum : u w = -1 := by
    rcases hupm w hwext with h | h
    · exact absurd (by rw [hHu]; exact ⟨hwP, h⟩) hwH
    · exact h
  have hnwH : -w ∈ H := by
    rw [hHu]
    refine ⟨hP.symm w hwP, ?_⟩
    rw [map_neg, hum]; norm_num
  have hnwW : -w ∈ W := by
    have h1 := hP.neg_extreme hwext
    rw [hPW] at h1
    exact Finset.mem_coe.1 (extremePoints_convexHull_subset h1)
  rcases hcov (-w) hnwW hnwH with h | h
  · exact hGRP (hP.eq_of_mem_of_neg_mem hGR (hTGR hwT) (hRGR h))
  · exact hGSP (hP.eq_of_mem_of_neg_mem hGS (hTGS hwT) (hSGS h))

end cs

end Kalai5
