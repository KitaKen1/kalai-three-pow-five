import Kalai5.Endpoints.PrismTriangles
import Kalai5.Endpoints.FullSixPartnerObstruction

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A vertex of a three-dimensional face lies in at least three polygons,
so polygons avoiding it must fit in the remaining slots. -/
theorem IsCSPolytope5.polygons_avoiding_vertex_capacity
    {T v : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3)
    (hv : v ∈ faces P) (hvT : v ⊆ T) (hv0 : dim v = 0)
    (A : Finset (Set E5))
    (hA : ∀ Q ∈ A, Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ ¬ v ⊆ Q) :
    A.card + 3 ≤ cnt P T 2 := by
  let S : Set (Set E5) := {Q | Q ∈ faces P ∧ v ⊆ Q ∧ Q ⊆ T ∧ dim Q = 2}
  have hSf : S.Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  obtain ⟨he,hl⟩ := hP.vertex_in_threeface hT hT3 hv hvT hv0
  have h3 : 3 ≤ S.ncard := by
    change vdeg P T v = S.ncard at he
    change 3 ≤ vdeg P T v at hl
    omega
  have hd : Disjoint (↑A : Set (Set E5)) S := by
    rw [Set.disjoint_left]
    intro Q hQA hQS
    exact (hA Q hQA).2.2.2 hQS.2.1
  have hs : (↑A : Set (Set E5)) ∪ S ⊆ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    rintro Q (hQ | hQ)
    · exact ⟨(hA Q hQ).1,(hA Q hQ).2.1,(hA Q hQ).2.2.1⟩
    · exact ⟨hQ.1,hQ.2.2⟩
  have hc := Set.ncard_le_ncard hs (hP.below_finite T 2)
  rw [Set.ncard_union_eq hd A.finite_toSet hSf,Set.ncard_coe_finset] at hc
  change A.card + S.ncard ≤ cnt P T 2 at hc
  omega

/-- A triangular prism has a second triangular face distinct from a given one. -/
theorem IsCSPolytope5.prism_other_triangle {T A : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (6,9,5)) :
    ∃ B, B ∈ faces P ∧ B ⊆ T ∧ dim B = 2 ∧ cnt P B 0 = 3 ∧ B ≠ A := by
  obtain ⟨hquad,hbig⟩ := hP.q4_695 hT hT3 ht
  have hp : cnt P T 2 = 5 := congrArg (fun t => t.2.2) ht
  let S := (hP.below_finite T 2).toFinset
  let N := S.filter (fun Q => cnt P Q 0 ≠ 4)
  have hSc : S.card = 5 := by rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset]; exact hp
  have hQc : (S.filter (fun Q => cnt P Q 0 = 4)).card = 3 := by rw [← hP.q4_eq_card]; exact hquad
  have hNc : N.card = 2 := by
    have he := Finset.card_filter_add_card_filter_not (s := S) (p := fun Q => cnt P Q 0 = 4)
    change (S.filter (fun Q => cnt P Q 0 = 4)).card + N.card = S.card at he
    omega
  have hm : ∀ Q ∈ N, Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 3 := by
    intro Q hQN
    obtain ⟨hQS,hn4⟩ := Finset.mem_filter.1 hQN
    rw [Set.Finite.mem_toFinset] at hQS
    obtain ⟨hQ,hQT,hQ2⟩ := hQS
    have hl := hP.three_le_cnt hQ hQ2
    have hn5 : ¬ 5 ≤ cnt P Q 0 := by
      intro hn
      have hfin : {U | U ∈ faces P ∧ U ⊆ T ∧ dim U = 2 ∧ 5 ≤ cnt P U 0}.Finite :=
        hP.faces_finite.subset fun U hU => hU.1
      have he : 0 < big2 P T := (Set.ncard_pos hfin).2 ⟨Q,hQ,hQT,hQ2,hn⟩
      omega
    exact ⟨hQ,hQT,hQ2,by omega⟩
  by_contra hn
  have hs : N ⊆ {A} := by
    intro Q hQ
    have he : Q = A := by
      by_contra hne
      exact hn ⟨Q,(hm Q hQ).1,(hm Q hQ).2.1,(hm Q hQ).2.2.1,(hm Q hQ).2.2.2,hne⟩
    simpa using he
  have hc := Finset.card_le_card hs
  rw [Finset.card_singleton,hNc] at hc
  omega

/-- A triangular face meets each quadrilateral of a triangular prism in two vertices. -/
theorem IsCSPolytope5.prism_triangle_quad_inter_two {T A Q : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (6,9,5))
    (hA : A ∈ faces P) (hAT : A ⊆ T) (hA2 : dim A = 2) (hA3 : cnt P A 0 = 3)
    (hQ : Q ∈ faces P) (hQT : Q ⊆ T) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    cnt P (A ∩ Q) 0 = 2 := by
  obtain ⟨B,hB,hBT,hB2,hB3,hBA⟩ := hP.prism_other_triangle (A := A) hT hT3 ht
  have hd := hP.prism_triangles_vertex_disjoint hT hT3 ht hA hAT hA2 hA3 hB hBT hB2 hB3 hBA.symm
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have he : vset P A ∪ vset P B = vset P T := by
    apply Set.eq_of_subset_of_ncard_le (Set.union_subset (vset_mono' hAT) (vset_mono' hBT)) _ (hP.vset_finite T)
    rw [Set.ncard_union_eq hd (hP.vset_finite A) (hP.vset_finite B),← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset]
    omega
  have hAQ : A ≠ Q := by intro he; rw [he] at hA3; omega
  have hBQ : B ≠ Q := by intro he; rw [he] at hB3; omega
  have ha := hP.polygon_common_vertices_le_two hA hA2 hQ hQ2 hAQ
  have hb := hP.polygon_common_vertices_le_two hB hB2 hQ hQ2 hBQ
  rw [← vset_inter',← cnt_eq_vset] at ha hb
  have hc : vset P Q ⊆ vset P (A ∩ Q) ∪ vset P (B ∩ Q) := by
    intro v hv
    have hvT := vset_mono' hQT hv
    rw [← he] at hvT
    rw [vset_inter',vset_inter']
    exact hvT.elim (fun h => Or.inl ⟨h,hv⟩) (fun h => Or.inr ⟨h,hv⟩)
  have hu := Set.ncard_le_ncard hc ((hP.vset_finite (A ∩ Q)).union (hP.vset_finite (B ∩ Q)))
  have hl := Set.ncard_union_le (vset P (A ∩ Q)) (vset P (B ∩ Q))
  rw [← cnt_eq_vset] at hu
  rw [← cnt_eq_vset,← cnt_eq_vset] at hl
  omega

end Kalai5
