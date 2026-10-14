import Kalai5.Endpoints.EventBudget

namespace Kalai5
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- In an eight-vertex facet with at least eight ridges, a positive
vertex-minus-polygon incidence gap forces a triangular prism. -/
theorem IsCSPolytope5.prism_positive_of_flag_gap {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (h8 : cnt P F 0 = 8)
    (hr : 8 ≤ cnt P F 3) (hgap : 2 * cnt P F 2 < incid P F 0 3) :
    1 ≤ tcnt P F (6,9,5) := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 h8
  have hz := hP.eight_ridges_no_7116 hF h4 h8 hr
  omega

theorem IsCSPolytope5.forced_prism_weight_nine {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,19,20,9,41⟩ ∨ faceRow P F = ⟨8,20,22,10,45⟩) :
    9 ≤ q55w P F + 2 * exc P F := by
  rcases hR with hR | hR
  all_goals
    have hn : cnt P F 0 = 8 := congrArg Row.n hR
    have hr := congrArg Row.r hR
    have hp := congrArg Row.p hR
    have hj := congrArg Row.J hR
    simp only [faceRow] at hr hp hj
    have ht := hP.prism_positive_of_flag_gap hF h4 hn (by omega) (by omega)
    have hl := (hP.prism_weight_lower hF h4 hn ht).2
    rw [hR] at hl
    norm_num [PrismBudget.prismLower,PrismBudget.rowExcess] at hl
    exact hl

def q55ForcedPrismRowWeight (R : Row) : ℕ :=
  if R = ⟨8,19,20,9,41⟩ ∨ R = ⟨8,20,22,10,45⟩ then 9 else q55QThreeRowWeight R

theorem IsCSPolytope5.q55_forcedPrism_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55ForcedPrismRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55ForcedPrismRowWeight
  split_ifs with he
  · exact hP.forced_prism_weight_nine hF h4 he
  · exact hP.q55_qThree_row_weight hF h4

theorem IsCSPolytope5.fewFull18_positive_forcedPrism_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((facetRows P).map q55ForcedPrismRowWeight).sum : ℤ) ≤ 156 - 6 * (flagDataOf P).Gs := by
  rw [hP.facetRows_sum q55ForcedPrismRowWeight,Nat.cast_sum]
  apply (Finset.sum_le_sum (fun F hF => ?_)).trans
    (hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt)
  rw [Set.Finite.mem_toFinset] at hF
  exact hP.q55_forcedPrism_row_weight hF.1 hF.2

theorem IsCSPolytope5.fewFull18_positive_forcedPrism_pair_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((positivePairRows P).map q55ForcedPrismRowWeight).sum : ℤ) ≤ 78 - 3 * (flagDataOf P).Gs := by
  have hb := hP.fewFull18_positive_forcedPrism_budget hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [(hp.map q55ForcedPrismRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hb
  omega

end Kalai5
