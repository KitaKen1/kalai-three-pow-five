import Kalai5.Endpoints.OnePairPrisms

/-!
# Vertex-set shortcuts for the one-pair configuration

Two distinct quadrilateral faces have at most two common vertices. In a
six-vertex prism they therefore share exactly two and together contain every
vertex. This replaces a labelled combinatorial model of the prism.
-/

namespace Kalai5

open Set
open scoped Classical

lemma vset_mono' {P A B : Set E5} (h : A ⊆ B) : vset P A ⊆ vset P B :=
  fun _ hv => ⟨hv.1, hv.2.1.trans h, hv.2.2⟩

lemma vset_inter' (P A B : Set E5) : vset P (A ∩ B) = vset P A ∩ vset P B := by
  ext v
  simp only [vset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.subset_inter_iff]
  tauto

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Distinct polygon faces share at most two vertices. -/
lemma IsCSPolytope5.polygon_common_vertices_le_two {Q R : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2)
    (hR : R ∈ faces P) (hR2 : dim R = 2) (hne : Q ≠ R) :
    (vset P Q ∩ vset P R).ncard ≤ 2 := by
  rw [← vset_inter', ← cnt_eq_vset]
  by_cases hi : (Q ∩ R).Nonempty
  · have hI := inter_mem_faces_of_nonempty hQ hR hi
    have hIQ : Q ∩ R ∈ faces Q := mem_faces_of_subset (face_subset hQ) hI inter_subset_left
    have hneI : Q ∩ R ≠ Q := by
      intro h
      apply hne
      exact hP.eq_of_subset_of_dim_le hQ hR
        (by rw [← h]; exact inter_subset_right) (by omega)
    have hd := dim_lt_of_mem_faces_ne hIQ hneI
    exact hP.cnt_le_two_of_dim_le_one hI (by omega)
  · have he : vset P (Q ∩ R) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro v hv
      exact hi (hv.1.1.mono hv.2.1)
    rw [cnt_eq_vset, he, Set.ncard_empty]
    omega

/-- Two quadrilaterals in a six-vertex face cover all six vertices and share two. -/
theorem IsCSPolytope5.six_vertex_quad_pair {K Q R : Set E5}
    (hK6 : cnt P K 0 = 6)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4)
    (hne : Q ≠ R) :
    vset P Q ∪ vset P R = vset P K ∧ (vset P Q ∩ vset P R).ncard = 2 ∧
      vset P K \ vset P Q ⊆ vset P R := by
  have hi := hP.polygon_common_vertices_le_two hQ hQ2 hR hR2 hne
  have hsum := Set.ncard_union_add_ncard_inter (vset P Q) (vset P R)
    (hP.vset_finite Q) (hP.vset_finite R)
  have hs : vset P Q ∪ vset P R ⊆ vset P K :=
    Set.union_subset (vset_mono' hQK) (vset_mono' hRK)
  have hc := Set.ncard_le_ncard hs (hP.vset_finite K)
  have hQv : (vset P Q).ncard = 4 := hQ4
  have hRv : (vset P R).ncard = 4 := hR4
  have hKv : (vset P K).ncard = 6 := hK6
  have heq : vset P Q ∪ vset P R = vset P K :=
    Set.eq_of_subset_of_ncard_le hs (by omega) (hP.vset_finite K)
  refine ⟨heq, by omega, ?_⟩
  intro v hv
  rw [← heq] at hv
  exact hv.1.resolve_left hv.2

/-- A facet all of whose ridges have at most one quadrilateral cannot share
two quadrilaterals with a distinct facet. -/
theorem IsCSPolytope5.shared_quad_unique {F X Q R : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hX : X ∈ faces P) (hX4 : dim X = 4)
    (hFX : F ≠ X)
    (hsmall : ∀ T ∈ faces P, T ⊆ F → dim T = 3 → q4 P T ≤ 1)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (hQX : Q ⊆ X) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hRX : R ⊆ X) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) :
    Q = R := by
  have hI : F ∩ X ∈ faces P :=
    inter_mem_faces_of_nonempty hF hX (hQ.1.mono (subset_inter hQF hQX))
  have hIF : F ∩ X ∈ faces F := mem_faces_of_subset (face_subset hF) hI inter_subset_left
  have hneI : F ∩ X ≠ F := by
    intro h
    exact hFX (hP.eq_of_subset_of_dim_le hF hX
      (by rw [← h]; exact inter_subset_right) (by omega))
  have hd := dim_lt_of_mem_faces_ne hIF hneI
  by_cases h2 : dim (F ∩ X) ≤ 2
  · have hQI := hP.eq_of_subset_of_dim_le hQ hI (subset_inter hQF hQX) (by omega)
    have hRI := hP.eq_of_subset_of_dim_le hR hI (subset_inter hRF hRX) (by omega)
    exact hQI.trans hRI.symm
  · have hq := hsmall (F ∩ X) hI inter_subset_left (by omega)
    by_contra hne
    have hs : ({Q, R} : Set (Set E5)) ⊆
        {U | U ∈ faces P ∧ U ⊆ F ∩ X ∧ dim U = 2 ∧ cnt P U 0 = 4} := by
      intro U hU
      rcases (show U = Q ∨ U = R by simpa using hU) with rfl | rfl
      · exact ⟨hQ, subset_inter hQF hQX, hQ2, hQ4⟩
      · exact ⟨hR, subset_inter hRF hRX, hR2, hR4⟩
    have hl := Set.ncard_le_ncard hs (hP.faces_finite.subset fun U hU => hU.1)
    rw [Set.ncard_pair hne] at hl
    change 2 ≤ q4 P (F ∩ X) at hl
    omega

/-- A full H in the residual configuration shares at most one quadrilateral
with any other facet. This makes the Y partners for its two quadrilaterals disjoint. -/
theorem IsCSPolytope5.fewFull18_one_pair_H_shared_quad_unique
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {F X Q R : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hrow : faceRow P F = OnePairProfile.fullRow 20)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hFX : F ≠ X)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (hQX : Q ⊆ X) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hRX : R ⊆ X) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) :
    Q = R := by
  apply hP.shared_quad_unique hF hF4 hX hX4 hFX ?_ hQ hQF hQX hQ2 hQ4 hR hRF hRX hR2 hR4
  intro T hT hTF hT3
  rcases (hP.fewFull18_one_pair_full_types hv hh hc hlt hF hF4 hrow).2.2.2 T hT hTF hT3 with ht | ht | ht
  · rw [hP.q4_464 hT hT3 ht]; omega
  · rw [(hP.q4_585 hT hT3 ht).1]
  · rw [(hP.q4_596 hT hT3 ht).1]; omega

end Kalai5
