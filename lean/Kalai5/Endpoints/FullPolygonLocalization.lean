import Kalai5.Endpoints.FullCrossVertices
import Kalai5.Endpoints.PolygonPairSupport

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A proper intersection with a polygon has at most two vertices. -/
theorem IsCSPolytope5.polygon_inter_vertices_le_two_of_not_subset {Q H : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hH : H ∈ faces P) (hn : ¬ Q ⊆ H) :
    cnt P (Q ∩ H) 0 ≤ 2 := by
  by_cases hi : (Q ∩ H).Nonempty
  · have hI := inter_mem_faces_of_nonempty hQ hH hi
    have hIQ := mem_faces_of_subset (face_subset hQ) hI inter_subset_left
    have hne : Q ∩ H ≠ Q := by
      intro he
      exact hn (by rw [← he]; exact inter_subset_right)
    have hd := dim_lt_of_mem_faces_ne hIQ hne
    exact hP.cnt_le_two_of_dim_le_one hI (by omega)
  · have he : vset P (Q ∩ H) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro v hv
      exact hi (hv.1.1.mono hv.2.1)
    rw [cnt_eq_vset,he,Set.ncard_empty]
    omega

/-- Every polygon with at least five vertices lies entirely in one sign
of any full proper face: otherwise its two proper intersections have at
most two vertices each. -/
theorem IsCSPolytope5.large_polygon_sub_full_or_neg {Q H : Set E5}
    (hH : H ∈ faces P) (hHP : H ≠ P) (hfull : 2 * cnt P H 0 = fvec P 0)
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ5 : 5 ≤ cnt P Q 0) :
    Q ⊆ H ∨ Q ⊆ -H := by
  by_contra hn
  have hnH : ¬ Q ⊆ H := fun h => hn (Or.inl h)
  have hnnH : ¬ Q ⊆ -H := fun h => hn (Or.inr h)
  have h1 := hP.polygon_inter_vertices_le_two_of_not_subset hQ hQ2 hH hnH
  have h2 := hP.polygon_inter_vertices_le_two_of_not_subset hQ hQ2
    (neg_mem_faces hP.symm hH) hnnH
  have hs : vset P Q ⊆ vset P (Q ∩ H) ∪ vset P (Q ∩ -H) := by
    intro v hv
    rw [vset_inter',vset_inter']
    rcases hP.vertex_mem_or_neg_mem_of_full hH hHP hfull hv.1 hv.2.2 with h | h
    · exact Or.inl ⟨hv,hv.1,h,hv.2.2⟩
    · exact Or.inr ⟨hv,hv.1,neg_subset_iff.2 h,hv.2.2⟩
  have hc := Set.ncard_le_ncard hs ((hP.vset_finite (Q ∩ H)).union (hP.vset_finite (Q ∩ -H)))
  have hu := Set.ncard_union_le (vset P (Q ∩ H)) (vset P (Q ∩ -H))
  rw [← cnt_eq_vset] at hc
  rw [← cnt_eq_vset,← cnt_eq_vset] at hu
  omega

/-- A full facet without large polygons excludes large polygons everywhere. -/
theorem IsCSPolytope5.big2_zero_of_full_facet {H : Set E5}
    (hH : H ∈ faces P) (h4 : dim H = 4) (hfull : 2 * cnt P H 0 = fvec P 0)
    (hz : big2 P H = 0) (F : Set E5) : big2 P F = 0 := by
  by_contra hn
  obtain ⟨Q,hQ,_,hQ2,hQ5⟩ := Set.nonempty_of_ncard_ne_zero hn
  have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [h4]; decide)
  have hfin : {Q | Q ∈ faces P ∧ Q ⊆ H ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hpos : 0 < big2 P H := by
    apply (Set.ncard_pos hfin).2
    rcases hP.large_polygon_sub_full_or_neg hH hHP hfull hQ hQ2 hQ5 with hs | hs
    · exact ⟨Q,hQ,hs,hQ2,hQ5⟩
    · exact ⟨-Q,neg_mem_faces hP.symm hQ,neg_subset_iff.1 hs,
        by rw [dim_neg,hQ2],by rw [hP.cnt_neg]; exact hQ5⟩
  omega

end Kalai5
