import Kalai5.Endpoints.RidgeExcess
import Kalai5.Endpoints.SinglePairSupport

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def bSpecialFree (R : Row) : Prop := R ∈ specialFreeRows ∨ rowExcess R < 2

instance (R : Row) : Decidable (bSpecialFree R) := by
  unfold bSpecialFree
  infer_instance

def bSupportOK (S : ℤ) (rows : List Row) : Bool :=
  decide (0 < pairSlack S rows) ||
    singleSupportOK ⟨8,19,19,8,38⟩ (rows.filter fun R => decide (bSpecialFree R)) rows

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

set_option maxHeartbeats 2000000 in
/-- A B facet of weight at most six has no prism. Its zero flag gap then
forces a (6,10,6) or (7,12,7) ridge, unless it has the impossible two-tetrahedra profile. -/
theorem IsCSPolytope5.b_weight_six_special_ridge {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,38⟩)
    (hw : q55w P F + 2 * exc P F ≤ 6) :
    1 ≤ tcnt P F (6,10,6) ∨ 1 ≤ tcnt P F (7,12,7) := by
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hr : cnt P F 3 = 8 := congrArg Row.r hR
  have hp : cnt P F 2 = 19 := congrArg Row.p hR
  have hj : incid P F 0 3 = 38 := congrArg Row.J hR
  have hpr : tcnt P F (6,9,5) = 0 := by
    by_contra hz
    have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
    rw [hR] at hl
    norm_num [PrismBudget.prismLower,PrismBudget.rowExcess] at hl
    omega
  have h7 := hP.eight_ridges_no_7116 hF h4 hn (by omega)
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  by_contra hbad
  have h610 : tcnt P F (6,10,6) = 0 := by omega
  have h712 : tcnt P F (7,12,7) = 0 := by omega
  have ht : tcnt P F (4,6,4) = 2 := by omega
  have hpy : tcnt P F (5,8,5) = 6 := by omega
  apply hP.not_two_tetrahedra_pyramids hF h4 ht
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

theorem IsCSPolytope5.b_special_free_counts {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.bSpecialFree (faceRow P F)) :
    tcnt P F (6,10,6) = 0 ∧ tcnt P F (7,12,7) = 0 := by
  rcases hR with hs | he
  · simp only [PrismBudget.specialFreeRows,List.mem_append,List.mem_singleton] at hs
    rcases hs with hs | h0
    · have hc : ∀ R ∈ PrismBudget.specialSmallFreeRows, R.n = 7 := by decide +kernel
      have hn : cnt P F 0 = 7 := hc _ hs
      exact ⟨(hP.small_special_free_counts hF h4 hs).1,
        hP.small_facet_seven_ridge_zero hF h4 hn.le 12 7⟩
    · obtain ⟨a,b,c,d,e,f⟩ := hP.r0_types hF h4 h0
      have hn : cnt P F 0 = 8 := congrArg Row.n h0
      have hr : cnt P F 3 = 7 := congrArg Row.r h0
      obtain ⟨c1,_,_,_⟩ := hP.facet8_arith hF h4 hn
      exact ⟨e,by omega⟩
  · have heq : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
    exact ⟨hP.tcnt_zero_of_exc_lt (by simp only; omega),
      hP.tcnt_zero_of_exc_lt (by simp only; omega)⟩

theorem IsCSPolytope5.b_single_support_budget {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.bSupportOK S rows = true := by
  by_cases hs : 0 < PrismBudget.pairSlack S rows
  · simp [PrismBudget.bSupportOK,hs]
  have hcheck : PrismBudget.singleSupportOK ⟨8,19,19,8,38⟩
      (rows.filter fun R => decide (PrismBudget.bSpecialFree R)) rows = true := by
    apply hP.single_pair_support_necessary _ _ [(6,10,6),(7,12,7)] hp
    · intro F hF h4 hR
      have hu := hP.facet_weight_le_of_pair_slack hp hb hF h4
      have hw : q55QThreeRowWeight ⟨8,19,19,8,38⟩ = 6 := by decide +kernel
      rw [hR,hw] at hu
      rcases hP.b_weight_six_special_ridge hF h4 hR (by omega) with h6 | h7
      · exact ⟨(6,10,6),by simp,h6⟩
      · exact ⟨(7,12,7),by simp,h7⟩
    · intro F hF h4 hR t ht
      have hh := hP.b_special_free_counts hF h4 (of_decide_eq_true (List.mem_filter.1 hR).2)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact hh.1
      · exact hh.2
  simp [PrismBudget.bSupportOK,hcheck]

end Kalai5
