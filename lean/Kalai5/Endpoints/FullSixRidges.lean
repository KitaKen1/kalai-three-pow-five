import Kalai5.Endpoints.OnePairVertices

/-!
# At most two six-vertex ridges in a full facet at zero stress

Two six-vertex ridges of an eight-vertex facet share at least four vertices.
A quadrilateral intersection would cover the full facet and force positive
stress. At zero stress they must instead share a pentagon. A six-vertex face
cannot contain two different pentagons, so three such ridges would violate
the fact that a polygon lies in exactly two ridges of the facet.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Distinct polygon faces in K have at most two common vertices. -/
lemma IsCSPolytope5.polygon_pair_vertex_budget {K Q R : Set E5}
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQ2 : dim Q = 2)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hne : Q ≠ R) :
    cnt P Q 0 + cnt P R 0 ≤ cnt P K 0 + 2 := by
  have hi := hP.polygon_common_vertices_le_two hQ hQ2 hR hR2 hne
  have hs := Set.ncard_union_add_ncard_inter (vset P Q) (vset P R)
    (hP.vset_finite Q) (hP.vset_finite R)
  have hu := Set.ncard_le_ncard (Set.union_subset (vset_mono' hQK) (vset_mono' hRK))
    (hP.vset_finite K)
  simp only [cnt_eq_vset]
  omega

/-- A six-vertex face cannot contain two different pentagonal faces. -/
lemma IsCSPolytope5.pentagon_unique_in_six {K Q R : Set E5} (hK6 : cnt P K 0 = 6)
    (hQ : Q ∈ faces P) (hQK : Q ⊆ K) (hQ2 : dim Q = 2) (hQ5 : cnt P Q 0 = 5)
    (hR : R ∈ faces P) (hRK : R ⊆ K) (hR2 : dim R = 2) (hR5 : cnt P R 0 = 5) : Q = R := by
  by_contra hne
  have := hP.polygon_pair_vertex_budget hQ hQK hQ2 hR hRK hR2 hne
  omega

/-- Distinct six-vertex ridges of a full facet at G=0 meet in a pentagon. -/
theorem IsCSPolytope5.six_ridges_inter_pentagon_G0
    (hv : fvec P 0 = 16) (hG : (flagDataOf P).G = 0)
    {F R S : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hR6 : cnt P R 0 = 6)
    (hS : S ∈ faces P) (hSF : S ⊆ F) (hS3 : dim S = 3) (hS6 : cnt P S 0 = 6) (hRS : R ≠ S) :
    R ∩ S ∈ faces P ∧ dim (R ∩ S) = 2 ∧ cnt P (R ∩ S) 0 = 5 := by
  have hu := Set.ncard_le_ncard (Set.union_subset (vset_mono' hRF) (vset_mono' hSF))
    (hP.vset_finite F)
  have hc := Set.ncard_union_add_ncard_inter (vset P R) (vset P S)
    (hP.vset_finite R) (hP.vset_finite S)
  rw [← vset_inter', ← cnt_eq_vset, ← cnt_eq_vset, ← cnt_eq_vset] at hc
  rw [← cnt_eq_vset] at hu
  have hI4 : 4 ≤ cnt P (R ∩ S) 0 := by omega
  have hne : (R ∩ S).Nonempty := by
    obtain ⟨v, hv⟩ := Set.nonempty_of_ncard_ne_zero
      (show (vset P (R ∩ S)).ncard ≠ 0 by rw [← cnt_eq_vset]; omega)
    exact hv.1.1.mono hv.2.1
  have hI := inter_mem_faces_of_nonempty hR hS hne
  have hIR : R ∩ S ∈ faces R := mem_faces_of_subset (face_subset hR) hI inter_subset_left
  have hIRne : R ∩ S ≠ R := by
    intro he
    exact hRS (hP.eq_of_subset_of_dim_le hR hS
      (by rw [← he]; exact inter_subset_right) (by omega))
  have hd := dim_lt_of_mem_faces_ne hIR hIRne
  have hI2 : dim (R ∩ S) = 2 := by
    by_contra hn
    have := hP.cnt_le_two_of_dim_le_one hI (by omega)
    omega
  have hlt := hP.cnt_zero_lt hI hR inter_subset_left hIRne
  refine ⟨hI, hI2, ?_⟩
  by_contra hn5
  have hQ4 : cnt P (R ∩ S) 0 = 4 := by omega
  have hg := hP.two_le_G_of_full_quad_counts hF hF4 (by omega) hI hI2 hQ4
    hR hR3 hRF hS hS3 hSF hRS inter_subset_left inter_subset_right (by omega)
  omega

/-- This local capacity bound needs no eight-vertex facet catalogue. -/
theorem IsCSPolytope5.six3_le_two_of_full_G0
    (hv : fvec P 0 = 16) (hG : (flagDataOf P).G = 0)
    {F : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8) :
    six3 P F ≤ 2 := by
  by_contra hbad
  have hfin : {R | R ∈ faces P ∧ dim R = 3 ∧ R ⊆ F ∧ cnt P R 0 = 6}.Finite :=
    hP.faces_finite.subset fun R hR => hR.1
  obtain ⟨R, S, T, hR, hS, hT, hRS, hRT, hST⟩ :=
    (Set.two_lt_ncard_iff hfin).1 (show 2 < six3 P F by omega)
  obtain ⟨hI, hI2, hI5⟩ := hP.six_ridges_inter_pentagon_G0 hv hG hF hF4 hF8
    hR.1 hR.2.2.1 hR.2.1 hR.2.2.2 hS.1 hS.2.2.1 hS.2.1 hS.2.2.2 hRS
  obtain ⟨hJ, hJ2, hJ5⟩ := hP.six_ridges_inter_pentagon_G0 hv hG hF hF4 hF8
    hR.1 hR.2.2.1 hR.2.1 hR.2.2.2 hT.1 hT.2.2.1 hT.2.1 hT.2.2.2 hRT
  have he := hP.pentagon_unique_in_six hR.2.2.2 hI inter_subset_left hI2 hI5
    hJ inter_subset_left hJ2 hJ5
  have hIT : R ∩ S ⊆ T := by rw [he]; exact inter_subset_right
  have hs : ({R, S, T} : Set (Set E5)) ⊆
      {U | U ∈ faces P ∧ R ∩ S ⊆ U ∧ U ⊆ F ∧ dim U = 3} := by
    intro U hU
    rcases hU with rfl | rfl | rfl
    · exact ⟨hR.1, inter_subset_left, hR.2.2.1, hR.2.1⟩
    · exact ⟨hS.1, inter_subset_right, hS.2.2.1, hS.2.1⟩
    · exact ⟨hT.1, hIT, hT.2.2.1, hT.2.1⟩
  have hl := Set.ncard_le_ncard hs (hP.faces_finite.subset fun U hU => hU.1)
  rw [Set.ncard_eq_three.2 ⟨R, S, T, hRS, hRT, hST, rfl⟩,
    hP.twoface_in_facet hF hF4 hI (inter_subset_left.trans hR.2.2.1) hI2] at hl
  omega

end Kalai5
