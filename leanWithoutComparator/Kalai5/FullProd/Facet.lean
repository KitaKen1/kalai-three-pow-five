import Kalai5.FullProd.Structure
import Kalai5.Gale.ClassifyX

/-!
# A facet with the row of `Δ2 × Δ2`

`IsCSPolytope5.prodTri_facet`: a facet of a centrally symmetric 5-polytope with row
`qRow = (9,18,15,6; 36)` has vertices `x a b` and facets (3-faces of `P`) `R i`, `C j` with the
incidences of `Δ2 × Δ2`.  Transported from `prodTri_structure` along the embedding of the facet's
affine hull.
-/

namespace Kalai5

open Set

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.prodTri_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = qRow) :
    ∃ (x : Fin 3 → Fin 3 → E5) (R C : Fin 3 → Set E5),
      (∀ a b a' b', x a b = x a' b' → a = a' ∧ b = b') ∧
      (∀ a b, x a b ∈ P.extremePoints ℝ ∧ x a b ∈ F) ∧
      (∀ z ∈ P.extremePoints ℝ, z ∈ F → ∃ a b, z = x a b) ∧
      (∀ i, R i ∈ faces P ∧ R i ⊆ F ∧ dim (R i) = 3) ∧
      (∀ j, C j ∈ faces P ∧ C j ⊆ F ∧ dim (C j) = 3) ∧
      (∀ a b i, x a b ∈ R i ↔ a ≠ i) ∧ (∀ a b j, x a b ∈ C j ↔ b ≠ j) := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hrowF : rowOf F = qRow := by rw [rowOf_face hF', ← hV]; exact hrow
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hFS hF.1
  have hrow' : rowOf (convexHull ℝ (V' : Set (E (dim F)))) = qRow := by
    rw [← hV', ← hrowF]
    simp only [rowOf, ← fvec_affEmb hp, ← flag2_affEmb hp]
  obtain ⟨x', R', C', hinj, hvert, hall, hR, hC, hxR, hxC⟩ := prodTri_structure h4 h0 hrow'
  have hFP : ∀ {G : Set (E (dim F))}, G ∈ faces (convexHull ℝ (V' : Set (E (dim F)))) →
      affEmb F p '' G ∈ faces P ∧ affEmb F p '' G ⊆ F := by
    intro G hG
    rw [← hV'] at hG
    have h1 := image_mem_faces hp hG
    refine ⟨?_, ?_⟩
    · rw [hV]
      exact faces_trans hF' h1
    · rintro _ ⟨z, hz, rfl⟩
      exact (face_subset hG hz : affEmb F p z ∈ F)
  refine ⟨fun a b => affEmb F p (x' a b), fun i => affEmb F p '' R' i,
    fun j => affEmb F p '' C' j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b a' b' h
    exact hinj a b a' b' (affEmb_injective (K := F) p h)
  · intro a b
    have hsing := singleton_mem_faces_of_extreme (hvert a b)
    have h1 := hFP hsing
    rw [Set.image_singleton] at h1
    exact ⟨mem_extremePoints_of_singleton_face h1.1, h1.2 (Set.mem_singleton _)⟩
  · intro z hz hzF
    have hzF' : z ∈ F.extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset (face_subset hF) ⟨hzF, hz⟩
    obtain ⟨z', rfl⟩ := exists_affEmb_eq hp hzF
    have hz' : z' ∈ (convexHull ℝ (V' : Set (E (dim F)))).extremePoints ℝ := by
      obtain ⟨y, hy⟩ : ∃ y, y = affEmb F p z' := ⟨_, rfl⟩
      have hyF : y ∈ F.extremePoints ℝ := by rw [hy]; exact hzF'
      have hzf : ({y} : Set E5) ∈ faces F := by
        rw [hFS] at hyF ⊢
        exact singleton_mem_faces_of_extreme hyF
      rw [hy] at hzf
      have h1 := preimage_mem_faces hp hzf
      have h2 : affEmb F p ⁻¹' {affEmb F p z'} = {z'} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => affEmb_injective (K := F) p h, fun h => by rw [h]⟩
      rw [h2, hV'] at h1
      exact mem_extremePoints_of_singleton_face h1
    obtain ⟨a, b, hab⟩ := hall z' hz'
    exact ⟨a, b, by rw [hab]⟩
  · intro i
    obtain ⟨h1, h2⟩ := hFP (hR i).1
    refine ⟨h1, h2, ?_⟩
    rw [dim_image_affEmb]
    exact (hR i).2
  · intro j
    obtain ⟨h1, h2⟩ := hFP (hC j).1
    refine ⟨h1, h2, ?_⟩
    rw [dim_image_affEmb]
    exact (hC j).2
  · intro a b i
    rw [(affEmb_injective (K := F) p).mem_set_image]
    exact hxR a b i
  · intro a b j
    rw [(affEmb_injective (K := F) p).mem_set_image]
    exact hxC a b j

end cs

end Kalai5
