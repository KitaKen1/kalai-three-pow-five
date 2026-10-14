import Kalai5.Endpoints.UniversalRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Every vertex of a triangular prism lies on two distinct quadrilaterals. -/
theorem IsCSPolytope5.prism_vertex_two_quads {T v : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (6,9,5))
    (hv : v ∈ faces P) (hvT : v ⊆ T) (hv0 : dim v = 0) :
    ∃ Q U, Q ≠ U ∧
      (Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4 ∧ v ⊆ Q) ∧
      (U ∈ faces P ∧ U ⊆ T ∧ dim U = 2 ∧ cnt P U 0 = 4 ∧ v ⊆ U) := by
  have ht6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  obtain ⟨Q,U,V,hQU,hQV,hUV,hset⟩ := Set.ncard_eq_three.1 (hP.q4_695 hT hT3 ht).1
  have mem (R : Set E5) (hR : R ∈ ({Q,U,V} : Set (Set E5))) :
      R ∈ faces P ∧ R ⊆ T ∧ dim R = 2 ∧ cnt P R 0 = 4 := by
    have hm : R ∈ {R | R ∈ faces P ∧ R ⊆ T ∧ dim R = 2 ∧ cnt P R 0 = 4} := by
      rw [hset]; exact hR
    exact hm
  have hQ := mem Q (by simp)
  have hU := mem U (by simp)
  have hV := mem V (by simp)
  have cover (A B : Set E5)
      (hA : A ∈ faces P ∧ A ⊆ T ∧ dim A = 2 ∧ cnt P A 0 = 4)
      (hB : B ∈ faces P ∧ B ⊆ T ∧ dim B = 2 ∧ cnt P B 0 = 4) (hne : A ≠ B) :
      v ⊆ A ∨ v ⊆ B := by
    have he := (hP.six_vertex_quad_pair ht6 hA.1 hA.2.1 hA.2.2.1 hA.2.2.2
      hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 hne).1
    have hm : v ∈ vset P A ∪ vset P B := he.symm ▸ ⟨hv,hvT,hv0⟩
    exact hm.elim (fun h => Or.inl h.2.1) (fun h => Or.inr h.2.1)
  by_cases hvQ : v ⊆ Q
  · by_cases hvU : v ⊆ U
    · exact ⟨Q,U,hQU,⟨hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2,hvQ⟩,
        ⟨hU.1,hU.2.1,hU.2.2.1,hU.2.2.2,hvU⟩⟩
    · have hvV := (cover U V hU hV hUV).resolve_left hvU
      exact ⟨Q,V,hQV,⟨hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2,hvQ⟩,
        ⟨hV.1,hV.2.1,hV.2.2.1,hV.2.2.2,hvV⟩⟩
  · have hvU := (cover Q U hQ hU hQU).resolve_left hvQ
    have hvV := (cover Q V hQ hV hQV).resolve_left hvQ
    exact ⟨U,V,hUV,⟨hU.1,hU.2.1,hU.2.2.1,hU.2.2.2,hvU⟩,
      ⟨hV.1,hV.2.1,hV.2.2.1,hV.2.2.2,hvV⟩⟩

/-- Distinct triangular faces of a triangular prism have disjoint vertex sets.
This uses vertex links and quadrilateral covers, without a labelled model. -/
theorem IsCSPolytope5.prism_triangles_vertex_disjoint {T A B : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (6,9,5))
    (hA : A ∈ faces P) (hAT : A ⊆ T) (hA2 : dim A = 2) (hA3 : cnt P A 0 = 3)
    (hB : B ∈ faces P) (hBT : B ⊆ T) (hB2 : dim B = 2) (hB3 : cnt P B 0 = 3)
    (hAB : A ≠ B) : Disjoint (vset P A) (vset P B) := by
  rw [Set.disjoint_left]
  intro v hva hvb
  obtain ⟨Q,U,hQU,hQ,hU⟩ := hP.prism_vertex_two_quads hT hT3 ht hva.1 (hva.2.1.trans hAT) hva.2.2
  have ne (R S : Set E5) (hR : cnt P R 0 = 3) (hS : cnt P S 0 = 4) : R ≠ S := by
    intro he; rw [he] at hR; omega
  have hfour : ({A,B,Q,U} : Set (Set E5)).ncard = 4 := Set.ncard_eq_four.2
    ⟨A,B,Q,U,hAB,ne A Q hA3 hQ.2.2.2.1,ne A U hA3 hU.2.2.2.1,
      ne B Q hB3 hQ.2.2.2.1,ne B U hB3 hU.2.2.2.1,hQU,rfl⟩
  have hs : ({A,B,Q,U} : Set (Set E5)) ⊆ {R | R ∈ faces P ∧ v ⊆ R ∧ R ⊆ T ∧ dim R = 2} := by
    intro R hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact ⟨hA,hva.2.1,hAT,hA2⟩
    · exact ⟨hB,hvb.2.1,hBT,hB2⟩
    · exact ⟨hQ.1,hQ.2.2.2.2,hQ.2.1,hQ.2.2.1⟩
    · exact ⟨hU.1,hU.2.2.2.2,hU.2.1,hU.2.2.1⟩
  have hc := (hP.vertex_in_threeface hT hT3 hva.1 (hva.2.1.trans hAT) hva.2.2).1
  change vdeg P T v = _ at hc
  have hf : 2 * cnt P T 1 = 3 * cnt P T 0 := by
    have hn : cnt P T 0 = 6 := congrArg Prod.fst ht
    have he : cnt P T 1 = 9 := congrArg (fun t => t.2.1) ht
    omega
  rw [hP.vdeg_eq_three hT hT3 hf hva.1 (hva.2.1.trans hAT) hva.2.2] at hc
  have hb := Set.ncard_le_ncard hs (hP.faces_finite.subset fun R hR => hR.1)
  rw [hfour,← hc] at hb
  omega

end Kalai5
