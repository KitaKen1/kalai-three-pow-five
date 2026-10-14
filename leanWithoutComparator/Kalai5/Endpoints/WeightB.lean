import Kalai5.Endpoints.TetraPyramidParity
import Kalai5.Endpoints.Weight8Basic

/-!
# Q55 weights three for B and C

Both rows have polygon excess three. A weight below three forces three
quadrilaterals, all of type (5,5). B then has two tetrahedra and six pyramids;
C has one tetrahedron, one bipyramid, and six pyramids. Both are excluded by
vertex parity, without a classification of eight-vertex facets.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Excess three has no intermediate quadrilateral count two. Consequently a
Q55 weight below three forces at least six square-pyramidal 3-faces. -/
lemma IsCSPolytope5.six_pyramids_of_exc_three {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hexc : exc P F = 3)
    (hbad : q55w P F + 2 * exc P F < 3) : 6 ≤ tcnt P F (5, 8, 5) := by
  have hq := hP.q4_add_big_le_exc F
  have hw := hP.q55w_ge F
  have hq3 : q4 P F = 3 := by
    have hq2 : 2 ≤ q4 P F := by omega
    have hb0 : big2 P F = 0 := by omega
    have he := hP.exc_eq_q4_of_big F hb0
    omega
  have he := hP.q55w_eq_b55 F
  have hb := hP.two_b55_le hF h4
  omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.q55_b_three {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 38⟩) :
    3 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hb := hP.two_b55_le hF h4
  have hq := hP.q55w_eq_b55 F
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero, add_zero] at hl
  by_contra hbad
  have hsix := hP.six_pyramids_of_exc_three hF h4 hexc (by omega)
  have ht : tcnt P F (4, 6, 4) = 2 := by omega
  have hy : tcnt P F (5, 8, 5) = 6 := by omega
  apply hP.not_two_tetrahedra_pyramids hF h4 ht
  intro T hT hTF hT3
  have h1 := hP.one_le_tcnt hT hTF hT3
  have hne : T ≠ F := by rintro rfl; omega
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | (left; rfl) | (right; rfl) | omega

/-- The previous weaker bound is retained for existing certificates. -/
theorem IsCSPolytope5.q55_b_pos {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 19, 19, 8, 38⟩) :
    1 ≤ q55w P F + 2 * exc P F := by
  have := hP.q55_b_three hF h4 hR
  omega

set_option maxHeartbeats 2000000 in
theorem IsCSPolytope5.q55_c_three {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8, 20, 20, 8, 39⟩) :
    3 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he, hp, hr, hJ⟩ := hR'
  obtain ⟨c1, c2, c3, -⟩ := hP.facet8_arith hF h4 hn
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hR] at hexc
  norm_num at hexc
  by_contra hbad
  have hsix := hP.six_pyramids_of_exc_three hF h4 hexc (by omega)
  have ht : tcnt P F (4, 6, 4) = 1 := by omega
  have hy : tcnt P F (5, 8, 5) = 6 := by omega
  have hb : tcnt P F (5, 9, 6) = 1 := by omega
  apply hP.not_one_tetrahedron_bipyramid_pyramids hF h4 ht hb
  intro T hT hTF hT3
  have h1 := hP.one_le_tcnt hT hTF hT3
  have hne : T ≠ F := by rintro rfl; omega
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

end Kalai5
