import Kalai5.Endpoints.OnePairVertices

/-!
# Facet intersections in a triangular upper link

If exactly three facets contain a polygon, any two of them share a ridge.
For a Y prism this identifies the other ridge through each quadrilateral,
and its five vertices give a vertex cover of Y by that ridge and the prism.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Any pair of facets in a triangular upper link meet in a ridge. -/
theorem IsCSPolytope5.facet_inter_dim_three_of_up_three {Q F G : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2)
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hQF : Q ⊆ F)
    (hG : G ∈ faces P) (hG4 : dim G = 4) (hQG : Q ⊆ G) (hFG : F ≠ G)
    (hthree : {X | X ∈ faces P ∧ Q ⊆ X ∧ dim X = 4}.ncard = 3) :
    dim (F ∩ G) = 3 := by
  obtain ⟨R, S, hR, hR3, hRF, hQR, hS, hS3, hSF, hQS, hRS, -⟩ :=
    hP.exists_two_three hF hF4 hQ hQF hQ2
  obtain ⟨A, hA, hA4, hAF, hRA⟩ := hP.exists_other_facet hR hR3 hRF
  obtain ⟨B, hB, hB4, hBF, hSB⟩ := hP.exists_other_facet hS hS3 hSF
  have hRI := hP.three_face_eq_inter hF hF4 hA hA4 hAF.symm hR hR3 hRF hRA
  have hSI := hP.three_face_eq_inter hF hF4 hB hB4 hBF.symm hS hS3 hSF hSB
  have hAB : A ≠ B := by intro h; exact hRS (hRI.trans (h ▸ hSI.symm))
  have hs : ({F, A, B} : Set (Set E5)) ⊆
      {X | X ∈ faces P ∧ Q ⊆ X ∧ dim X = 4} := by
    intro X hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨hF, hQF, hF4⟩
    · exact ⟨hA, hQR.trans hRA, hA4⟩
    · exact ⟨hB, hQS.trans hSB, hB4⟩
  have hcard : ({F, A, B} : Set (Set E5)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨F, A, B, hAF.symm, hBF.symm, hAB, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hs (by rw [hthree, hcard]) (hP.above_finite Q 4)
  have hg : G ∈ ({F, A, B} : Set (Set E5)) := by
    rw [heq]; exact ⟨hG, hQG, hG4⟩
  rcases hg with h | rfl | rfl
  · exact False.elim (hFG h.symm)
  · rwa [← hRI]
  · rwa [← hSI]

/-- The other ridge through a quadrilateral of a six-vertex ridge has five
vertices, provided its upper link has only three facets. -/
lemma IsCSPolytope5.five_vertices_beside_six (hv : fvec P 0 = 16)
    {Y K T Q : Set E5} (hY : Y ∈ faces P) (hY4 : dim Y = 4)
    (hK : K ∈ faces P) (hKY : K ⊆ Y) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6)
    (hT : T ∈ faces P) (hTY : T ⊆ Y) (hT3 : dim T = 3) (hKT : K ≠ T)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQT : Q ⊆ T) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hthree : {X | X ∈ faces P ∧ Q ⊆ X ∧ dim X = 4}.ncard = 3) :
    cnt P T 0 = 5 := by
  have hn := hP.non5_le_one hv hY hY4 hQ (hQK.trans hKY) hQ2 hQ4 hthree
  by_contra ht
  have hs : ({K, T} : Set (Set E5)) ⊆ non5 P Y Q := by
    intro U hU
    rcases hU with rfl | rfl
    · exact ⟨hK, hKY, hK3, hQK, by omega⟩
    · exact ⟨hT, hTY, hT3, hQT, ht⟩
  have hl := Set.ncard_le_ncard hs (hP.non5_finite Y Q)
  rw [Set.ncard_pair hKT] at hl
  omega

/-- Cardinality forces a seven-vertex facet to be covered by its six- and
five-vertex ridges through a quadrilateral. -/
lemma IsCSPolytope5.seven_vertex_ridge_cover {Y K T Q : Set E5}
    (hY7 : cnt P Y 0 = 7) (hK6 : cnt P K 0 = 6) (hT5 : cnt P T 0 = 5)
    (hQ4 : cnt P Q 0 = 4) (hKY : K ⊆ Y) (hTY : T ⊆ Y) (hinter : K ∩ T = Q) :
    vset P K ∪ vset P T = vset P Y ∧
      vset P Y \ vset P K = vset P T \ vset P Q ∧
      (vset P Y \ vset P K).ncard = 1 := by
  obtain ⟨hadd, hsub⟩ := hP.cnt_add_le hKY hTY hinter
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (show (vset P Y).ncard ≤ (vset P K ∪ vset P T).ncard by
      rw [← cnt_eq_vset]; omega) (hP.vset_finite Y)
  refine ⟨heq, ?_, ?_⟩
  · have hi : vset P K ∩ vset P T = vset P Q := by rw [← vset_inter', hinter]
    rw [← heq, ← hi]
    ext v
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
    tauto
  · rw [Set.ncard_sdiff (vset_mono' hKY) (hP.vset_finite K),
      ← cnt_eq_vset, ← cnt_eq_vset, hY7, hK6]

/-- The extra vertex of Y outside its prism belongs to every third facet
through any quadrilateral of the prism. -/
theorem IsCSPolytope5.fewFull18_one_pair_Y_apex_in_third
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {Y Z K X Q : Set E5}
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYrow : faceRow P Y = excRow)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hYZ : Y ≠ Z)
    (hK : K ∈ faces P) (hK3 : dim K = 3) (hK6 : cnt P K 0 = 6) (hKI : K = Y ∩ Z)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hXY : X ≠ Y) (hXZ : X ≠ Z)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQX : Q ⊆ X) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    dim (Y ∩ X) = 3 ∧ cnt P (Y ∩ X) 0 = 5 ∧ K ∩ X = Q ∧
      (vset P Y \ vset P K).ncard = 1 ∧ vset P Y \ vset P K ⊆ vset P X := by
  have hKY : K ⊆ Y := hKI ▸ inter_subset_left
  have hKZ : K ⊆ Z := hKI ▸ inter_subset_right
  have hthree := hP.quad_up_eq_three_of_G_eq_zero
    (hP.fewFull18_one_pair_stresses hv hh hc hlt).1 hQ hQ2 hQ4
  have hT : Y ∩ X ∈ faces P :=
    inter_mem_faces_of_nonempty hY hX (hQ.1.mono (subset_inter (hQK.trans hKY) hQX))
  have hT3 := hP.facet_inter_dim_three_of_up_three hQ hQ2 hY hY4 (hQK.trans hKY)
    hX hX4 hQX hXY.symm hthree
  have hKT : K ≠ Y ∩ X := by
    intro he
    have hKX : K ⊆ X := he ▸ inter_subset_right
    have h2 := hP.ridge_two hK hK3
    have hs : ({Y, Z, X} : Set (Set E5)) ⊆ {F | F ∈ faces P ∧ K ⊆ F ∧ dim F = 4} := by
      intro F hF
      rcases hF with rfl | rfl | rfl
      · exact ⟨hY, hKY, hY4⟩
      · exact ⟨hZ, hKZ, hZ4⟩
      · exact ⟨hX, hKX, hX4⟩
    have hl := Set.ncard_le_ncard hs (hP.above_finite K 4)
    rw [Set.ncard_eq_three.2 ⟨Y, Z, X, hYZ, hXY.symm, hXZ.symm, rfl⟩, h2] at hl
    omega
  have hT5 := hP.five_vertices_beside_six hv hY hY4 hK hKY hK3 hK6
    hT inter_subset_left hT3 hKT hQ hQK (subset_inter (hQK.trans hKY) hQX) hQ2 hQ4 hthree
  have hi := hP.inter_three_eq hQ hQ2 hK hK3 hT hT3 hKT hQK
    (subset_inter (hQK.trans hKY) hQX)
  have hiX : K ∩ X = Q := by
    rw [← hi]
    ext x
    simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.1, hKY h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  obtain ⟨-, hd, hn⟩ := hP.seven_vertex_ridge_cover (congrArg Row.n hYrow)
    hK6 hT5 hQ4 hKY inter_subset_left hi
  refine ⟨hT3, hT5, hiX, hn, ?_⟩
  rw [hd]
  exact fun _ hv => ⟨hv.1.1, hv.1.2.1.trans inter_subset_right, hv.1.2.2⟩

end Kalai5
