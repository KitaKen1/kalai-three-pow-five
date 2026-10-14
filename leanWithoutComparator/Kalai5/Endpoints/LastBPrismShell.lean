import Kalai5.Endpoints.G2S2LastSixClosure
import Kalai5.Endpoints.PrismTriangleQuad
import Kalai5.Endpoints.TwoPairZeroB19Apices

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- In eight vertices, a triangular bipyramid and a triangular prism
meet in a triangle and together cover all vertices. -/
theorem IsCSPolytope5.bipyr_prism_vertex_cover {F T R : Set E5}
    (hF8 : cnt P F 0 = 8)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (5,9,6))
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hr : tri3 P R = (6,9,5)) :
    T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 ∧ cnt P (T ∩ R) 0 = 3 ∧
      vset P T ∪ vset P R = vset P F := by
  have hT5 : cnt P T 0 = 5 := congrArg Prod.fst ht
  have hR6 : cnt P R 0 = 6 := congrArg Prod.fst hr
  have hTR : T ≠ R := by intro he; rw [he] at hT5; omega
  obtain ⟨hI,hI2⟩ := hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hR hRF hR3 hTR (by omega)
  have hl := hP.three_le_cnt hI hI2
  have hu := hP.cnt_zero_lt hI hT inter_subset_left (by intro he; rw [he,hT3] at hI2; omega)
  have hI3 : cnt P (T ∩ R) 0 = 3 := by
    by_contra hn
    have hf : {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.Finite :=
      hP.faces_finite.subset fun Q hQ => hQ.1
    have hp : 0 < q4 P T := (Set.ncard_pos hf).2 ⟨T ∩ R,hI,inter_subset_left,hI2,by omega⟩
    rw [(hP.q4_596 hT hT3 ht).1] at hp
    omega
  refine ⟨hI,hI2,hI3,?_⟩
  have hc := Set.ncard_union_add_ncard_inter (vset P T) (vset P R) (hP.vset_finite T) (hP.vset_finite R)
  rw [← vset_inter',← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset] at hc
  apply Set.eq_of_subset_of_ncard_le (Set.union_subset (vset_mono' hTF) (vset_mono' hRF)) _ (hP.vset_finite F)
  rw [← cnt_eq_vset]
  omega

/-- Every quadrilateral of the sole prism is shared with a square pyramid. -/
theorem IsCSPolytope5.last_b_prism_quad_pyramid {F R Q : Set E5}
    (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hprof : fv8.map (tcnt P F) = [3,3,1,1,0,0,0,0,0,0,0,0])
    (hR : R ∈ faces P) (hRF : R ⊆ F) (hR3 : dim R = 3) (hr : tri3 P R = (6,9,5))
    (hQ : Q ∈ faces P) (hQR : Q ⊆ R) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    ∃ Y, Y ∈ faces P ∧ Y ⊆ F ∧ dim Y = 3 ∧ tri3 P Y = (5,8,5) ∧ Q = R ∩ Y := by
  obtain ⟨Y,⟨hY,hQY,hYF,hY3⟩,hYR⟩ := exists_ne_of_ncard_eq_two
    (hP.twoface_in_facet hF hF4 hQ (hQR.trans hRF) hQ2) ⟨hR,hQR,hRF,hR3⟩
  have hQI : Q = R ∩ Y := (hP.inter_three_eq hQ hQ2 hR hR3 hY hY3 hYR.symm hQR hQY).symm
  have hpY : 0 < q4 P Y := (Set.ncard_pos (hP.faces_finite.subset fun Q hQ => hQ.1)).2
    ⟨Q,hQ,hQY,hQ2,hQ4⟩
  have hc := hprof
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hc
  have hlt := hP.cnt_zero_lt hY hF hYF (by intro he; rw [he,hF4] at hY3; omega)
  have hm := hP.tri3_mem_fv8 hY hY3 (by omega)
  have hpos := hP.one_le_tcnt hY hYF hY3
  have hpy : tri3 P Y = (5,8,5) := by
    simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h
    · rw [hP.q4_464 hY hY3 h] at hpY; omega
    · exact h
    · rw [(hP.q4_596 hY hY3 h).1] at hpY; omega
    · have hfin : {S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3 ∧ tri3 P S = (6,9,5)}.Finite :=
        hP.faces_finite.subset fun S hS => hS.1
      have hle : {S | S ∈ faces P ∧ S ⊆ F ∧ dim S = 3 ∧ tri3 P S = (6,9,5)}.ncard ≤ 1 := by
        change tcnt P F (6,9,5) ≤ 1; omega
      exact (hYR ((Set.ncard_le_one hfin).1 hle Y ⟨hY,hYF,hY3,h⟩ R ⟨hR,hRF,hR3,hr⟩)).elim
    all_goals rw [h] at hpos; omega
  exact ⟨Y,hY,hYF,hY3,hpy,hQI⟩

/-- The apex opposite a prism quadrilateral lies in the bipyramid and
outside the prism. This leaves only two possible apex vertices. -/
theorem IsCSPolytope5.bipyr_prism_pyramid_apex {F T R Q Y : Set E5}
    (hcover : vset P T ∪ vset P R = vset P F) (hYF : Y ⊆ F)
    (hy : tri3 P Y = (5,8,5)) (hQ4 : cnt P Q 0 = 4) (hQI : Q = R ∩ Y) :
    ∃ a, a ∈ vset P T ∧ a ∉ vset P R ∧ vset P Y = insert a (vset P Q) := by
  have hY5 : cnt P Y 0 = 5 := congrArg Prod.fst hy
  have hQY : Q ⊆ Y := hQI ▸ inter_subset_right
  obtain ⟨a,ha,haQ,he⟩ := hP.polygon_pyramid_apex hQY (by omega)
  have haR : a ∉ vset P R := by
    intro haR
    apply haQ
    rw [hQI,vset_inter']
    exact ⟨haR,ha⟩
  have haT : a ∈ vset P T := by
    have hm := vset_mono' hYF ha
    rw [← hcover] at hm
    exact hm.resolve_right haR
  exact ⟨a,haT,haR,he⟩

end Kalai5
