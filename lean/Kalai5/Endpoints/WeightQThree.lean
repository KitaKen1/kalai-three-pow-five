import Kalai5.Endpoints.ThreeTetraEdgeObstruction

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

set_option maxHeartbeats 2000000 in
/-- The Q row has weight at least three. A smaller weight forces six
square pyramids and three tetrahedra, which need at least twenty-two edges. -/
theorem IsCSPolytope5.q_weight_three {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,20,21,9,42⟩) :
    3 ≤ q55w P F + 2 * exc P F := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have he20 : cnt P F 1 = 20 := congrArg Row.e hR
  have hr : cnt P F 3 = 9 := congrArg Row.r hR
  have hj : incid P F 0 3 = 42 := congrArg Row.J hR
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have hb := hP.two_b55_le hF h4
  have hw := hP.q55w_eq_b55 F
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hq := hP.q4_add_big_le_exc F
  have hq2 : q4 P F ≠ 2 := by
    intro htwo
    have hz : big2 P F = 0 := by omega
    have := hP.exc_eq_q4_of_big F hz
    omega
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero,add_zero] at hl
  by_contra hbad
  have hpyr : tcnt P F (5,8,5) = 6 := by omega
  have ht : tcnt P F (4,6,4) = 3 := by omega
  have htypes : ∀ T ∈ faces P, T ⊆ F → dim T = 3 →
      tri3 P T = (4,6,4) ∨ tri3 P T = (5,8,5) := by
    intro T hT hTF hT3
    have hne : T ≠ F := by intro heq; rw [heq,h4] at hT3; omega
    have hlt := hP.cnt_zero_lt hT hF hTF hne
    have hm := hP.tri3_mem_fv8 hT hT3 (by omega)
    have hpos := hP.one_le_tcnt hT hTF hT3
    simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    all_goals rw [h] at hpos; omega
  have hedge := hP.three_tetrahedra_edges_twenty_two hF h4 hn ht htypes
  omega

/-- Add the Q lower bound to the previously certified V lower bound. -/
def q55QThreeRowWeight (R : Row) : ℕ :=
  if R = ⟨8,20,21,9,42⟩ then 3 else q55VTwelveRowWeight R

theorem IsCSPolytope5.q55_qThree_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55QThreeRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55QThreeRowWeight
  split_ifs with he
  · exact hP.q_weight_three hF h4 he
  · exact hP.q55_vTwelve_row_weight hF h4

theorem IsCSPolytope5.fewFull18_positive_qThree_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((facetRows P).map q55QThreeRowWeight).sum : ℤ) ≤ 156 - 6 * (flagDataOf P).Gs := by
  rw [hP.facetRows_sum q55QThreeRowWeight,Nat.cast_sum]
  apply (Finset.sum_le_sum (fun F hF => ?_)).trans
    (hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt)
  rw [Set.Finite.mem_toFinset] at hF
  exact hP.q55_qThree_row_weight hF.1 hF.2

theorem IsCSPolytope5.fewFull18_positive_qThree_pair_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((positivePairRows P).map q55QThreeRowWeight).sum : ℤ) ≤ 78 - 3 * (flagDataOf P).Gs := by
  have hb := hP.fewFull18_positive_qThree_budget hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [(hp.map q55QThreeRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hb
  omega

end Kalai5
