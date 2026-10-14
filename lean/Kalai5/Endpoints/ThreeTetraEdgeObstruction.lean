import Kalai5.Endpoints.ThreeTetraVertices
import Kalai5.Endpoints.FacetEdgeBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Three tetrahedra and otherwise square pyramids in an eight-vertex
facet force at least twenty-two edges. -/
theorem IsCSPolytope5.three_tetrahedra_edges_twenty_two
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (h8 : cnt P F 0 = 8)
    (hcnt : tcnt P F (4,6,4) = 3)
    (htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5)) : 22 ≤ cnt P F 1 := by
  obtain ⟨A,B,C,hAB,hAC,hBC,hs⟩ := Set.ncard_eq_three.1 hcnt
  have hA : A ∈ faces P ∧ A ⊆ F ∧ dim A = 3 ∧ tri3 P A = (4,6,4) := by
    change A ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inl rfl
  have hB : B ∈ faces P ∧ B ⊆ F ∧ dim B = 3 ∧ tri3 P B = (4,6,4) := by
    change B ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inr (Or.inl rfl)
  have hC : C ∈ faces P ∧ C ⊆ F ∧ dim C = 3 ∧ tri3 P C = (4,6,4) := by
    change C ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (4,6,4)}
    rw [hs]; exact Or.inr (Or.inr rfl)
  obtain ⟨hu,hab,hac,hbc⟩ := hP.three_tetra_vertex_counts hF h4 hAB hAC hBC hs htypes
  let U := vset P A ∪ vset P B ∪ vset P C
  let D := edgeSet P A ∪ edgeSet P B ∪ edgeSet P C
  have hf : U.Finite := ((hP.vset_finite A).union (hP.vset_finite B)).union (hP.vset_finite C)
  have hus : U ⊆ vset P F := Set.union_subset
    (Set.union_subset (vset_mono' hA.2.1) (vset_mono' hB.2.1)) (vset_mono' hC.2.1)
  have hout : (vset P F \ U).ncard = 2 := by
    rw [Set.ncard_sdiff hus hf,← cnt_eq_vset,h8]
    change 8 - (vset P A ∪ vset P B ∪ vset P C).ncard = 2
    rw [hu]
  obtain ⟨v,w,hvw,he⟩ := Set.ncard_eq_two.1 hout
  have hv : v ∈ vset P F \ U := by rw [he]; exact Or.inl rfl
  have hw : w ∈ vset P F \ U := by rw [he]; exact Or.inr rfl
  have hd : D ⊆ edgeSet P F := by
    rintro e ((he | he) | he)
    · exact ⟨he.1,he.2.1.trans hA.2.1,he.2.2⟩
    · exact ⟨he.1,he.2.1.trans hB.2.1,he.2.2⟩
    · exact ⟨he.1,he.2.1.trans hC.2.1,he.2.2⟩
  have hdu : ∀ e ∈ D, vset P e ⊆ U := by
    rintro e ((he | he) | he) x hx
    · exact Or.inl (Or.inl (vset_mono' he.2.1 hx))
    · exact Or.inl (Or.inr (vset_mono' he.2.1 hx))
    · exact Or.inr (vset_mono' he.2.1 hx)
  have ea : cnt P A 1 = 6 := congrArg (fun t => t.2.1) hA.2.2.2
  have eb : cnt P B 1 = 6 := congrArg (fun t => t.2.1) hB.2.2.2
  have ec : cnt P C 1 = 6 := congrArg (fun t => t.2.1) hC.2.2.2
  have hl : 15 ≤ D.ncard := hP.three_edge_sets_fifteen ea eb ec hab.le hac.le hbc.le
  exact hP.edges_twenty_two_of_core hF h4 hd hdu hl hv.1 hw.1 hvw hv.2 hw.2

end Kalai5
