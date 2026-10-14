import Kalai5.Endpoints.SinglePairSupport

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def no7116Row (R : Row) : Prop :=
  R.n ≤ 7 ∨ R = r0Row ∨ R = zRow ∨ (R.n = 8 ∧ 8 ≤ R.r)

instance (R : Row) : Decidable (no7116Row R) := by
  unfold no7116Row
  infer_instance

def r35PairBudgetOK (S : ℤ) (rows : List Row) : Bool :=
  decide (pairRowCount r35Row rows ≠ 1) ||
    !(rows.all fun R => decide (R = r35Row ∨ no7116Row R)) ||
    decide (2 ≤ pairSlack S rows)

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.no7116_row_count_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.no7116Row (faceRow P F)) : tcnt P F (7,11,6) = 0 := by
  rcases hR with hn | h0 | hz | ⟨hn,hr⟩
  · exact hP.small_facet_seven_ridge_zero hF h4 hn 11 6
  · exact (hP.r0_types hF h4 h0).2.2.2.2.2
  · exact (hP.r19_types hF h4 hz).2.2.2.2.2
  · exact hP.eight_ridges_no_7116 hF h4 hn hr

/-- A single R35 pair without another carrier of (7,11,6) must instead
have a prism. Its weight is at least twelve, costing two units of pair slack. -/
theorem IsCSPolytope5.r35_single_pair_budget {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.r35PairBudgetOK S rows = true := by
  by_cases hc : PrismBudget.pairRowCount r35Row rows ≠ 1
  · simp [PrismBudget.r35PairBudgetOK,hc]
  have hone : PrismBudget.pairRowCount r35Row rows = 1 := by omega
  by_cases hall : ∀ R ∈ rows, R = r35Row ∨ PrismBudget.no7116Row R
  · have hm : r35Row ∈ rows := by
      by_contra hn
      have hz : (rows.map fun R => if R = r35Row then 1 else 0).sum = (0 : ℕ) := by
        have he : rows.map (fun R => if R = r35Row then 1 else 0) = rows.map (fun _ => (0 : ℕ)) := by
          apply List.map_congr_left
          intro R hR
          rw [if_neg (fun h : R = r35Row => hn (h ▸ hR))]
        rw [he,List.map_const',List.sum_replicate]
        simp
      change PrismBudget.pairRowCount r35Row rows = 0 at hz
      omega
    obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hm))
    have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ r35Row →
        tcnt P H (7,11,6) = 0 := by
      intro H hH hH4 hne
      have hmH : faceRow P H ∈ rows := by
        have hmem : faceRow P H ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨H,Finset.mem_toList.2 (by
            rw [Set.Finite.mem_toFinset]; exact ⟨hH,hH4⟩),rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hmem
      exact hP.no7116_row_count_zero hH hH4 ((hall _ hmH).resolve_left hne)
    have hz := hP.tcnt_zero_of_unique_pair_row hp hone (7,11,6) hother hF h4
    have he := hP.r35_event_one hF h4 hR
    have hn : cnt P F 0 = 8 := congrArg Row.n hR
    have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
    rw [hR] at hl
    norm_num [PrismBudget.prismLower,PrismBudget.rowExcess,r35Row] at hl
    have hu := hP.facet_weight_le_of_pair_slack hp hb hF h4
    have hw : q55QThreeRowWeight r35Row = 10 := by decide +kernel
    rw [hR,hw] at hu
    have hs : 2 ≤ PrismBudget.pairSlack S rows := by omega
    simp [PrismBudget.r35PairBudgetOK,hs]
  · have hf : (rows.all fun R => decide (R = r35Row ∨ PrismBudget.no7116Row R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      exact hall (fun R hR => of_decide_eq_true ((List.all_eq_true.1 hh) R hR))
    simp only [PrismBudget.r35PairBudgetOK,hf,Bool.not_false,Bool.or_true,Bool.true_or]

end Kalai5
