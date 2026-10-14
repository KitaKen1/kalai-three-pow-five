import Kalai5.Endpoints.SinglePairBudget
import Kalai5.Endpoints.WeightQFour

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def qFourPairSlack (S : ℤ) (rows : List Row) : ℤ :=
  78 - 3 * S - (rows.map q55QFourRowWeight).sum

def r35QFourPairBudgetOK (S : ℤ) (rows : List Row) : Bool :=
  decide (pairRowCount r35Row rows ≠ 1) ||
    !(rows.all fun R => decide (R = r35Row ∨ no7116Row R)) ||
    decide (2 ≤ qFourPairSlack S rows)

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.facet_weight_le_of_qFour_pair_slack {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + PrismBudget.qFourPairSlack S rows := by
  have hu := hP.twice_facet_weight_le_of_lower_bound q55QFourRowWeight
    (fun _ => hP.q55_qFour_row_weight) (156 - 6 * S) hb hF h4
  rw [(hp.map q55QFourRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hu
  unfold PrismBudget.qFourPairSlack
  omega

/-- A single R35 pair without another carrier of (7,11,6) must instead
have a prism. Its weight is at least twelve, costing two units of pair slack. -/
theorem IsCSPolytope5.r35_single_pair_qFour_budget {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.r35QFourPairBudgetOK S rows = true := by
  by_cases hc : PrismBudget.pairRowCount r35Row rows ≠ 1
  · simp [PrismBudget.r35QFourPairBudgetOK,hc]
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
    have hu := hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4
    have hw : q55QFourRowWeight r35Row = 10 := by decide +kernel
    rw [hR,hw] at hu
    have hs : 2 ≤ PrismBudget.qFourPairSlack S rows := by omega
    simp [PrismBudget.r35QFourPairBudgetOK,hs]
  · have hf : (rows.all fun R => decide (R = r35Row ∨ PrismBudget.no7116Row R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      exact hall (fun R hR => of_decide_eq_true ((List.all_eq_true.1 hh) R hR))
    simp only [PrismBudget.r35QFourPairBudgetOK,hf,Bool.not_false,Bool.or_true,Bool.true_or]

end Kalai5
