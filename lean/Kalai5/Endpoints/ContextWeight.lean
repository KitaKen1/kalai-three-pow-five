import Kalai5.Endpoints.QFourPairBudget

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def r35Forced (rows : List Row) : Prop :=
  pairRowCount r35Row rows = 1 ∧
    (rows.all fun R => decide (R = r35Row ∨ no7116Row R)) = true

instance (rows : List Row) : Decidable (r35Forced rows) := by
  unfold r35Forced
  infer_instance

def contextRowWeight (rows : List Row) (R : Row) : ℕ :=
  if r35Forced rows ∧ R = r35Row then 12 else q55QFourRowWeight R

def contextPairSlack (S : ℤ) (rows : List Row) : ℤ :=
  78 - 3 * S - (rows.map (contextRowWeight rows)).sum

def contextUpper (S : ℤ) (rows : List Row) (R : Row) : ℤ :=
  (contextRowWeight rows R : ℤ) + contextPairSlack S rows

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.faceRow_mem_pair_rows {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) : faceRow P F ∈ rows := by
  have hm : faceRow P F ∈ facetRows P := by
    rw [hP.facetRows_eq]
    exact List.mem_map.2 ⟨F,Finset.mem_toList.2 (by
      rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩),rfl⟩
  simpa only [List.mem_append,or_self] using hp.mem_iff.1 hm

/-- Extract the conditional R35 lower bound so its cost can be charged
before distributing the remaining budget to the other row pairs. -/
theorem IsCSPolytope5.r35_forced_weight_twelve {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) (hf : PrismBudget.r35Forced rows)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    12 ≤ q55w P F + 2 * exc P F := by
  have hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ r35Row → tcnt P H (7,11,6) = 0 := by
    intro H hH hH4 hne
    have hm := hP.faceRow_mem_pair_rows hp hH hH4
    have hk := of_decide_eq_true ((List.all_eq_true.1 hf.2) _ hm)
    exact hP.no7116_row_count_zero hH hH4 (hk.resolve_left hne)
  have hz := hP.tcnt_zero_of_unique_pair_row hp hf.1 (7,11,6) hother hF h4
  have he := hP.r35_event_one hF h4 hR
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
  rw [hR] at hl
  norm_num [PrismBudget.prismLower,PrismBudget.rowExcess,r35Row] at hl
  exact hl

theorem IsCSPolytope5.context_row_weight_lower {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (PrismBudget.contextRowWeight rows (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold PrismBudget.contextRowWeight
  split_ifs with hh
  · exact hP.r35_forced_weight_twelve hp hh.1 hF h4 hh.2
  · exact hP.q55_qFour_row_weight hF h4

theorem IsCSPolytope5.facet_weight_le_context_upper {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ PrismBudget.contextUpper S rows (faceRow P F) := by
  have hu := hP.twice_facet_weight_le_of_lower_bound (PrismBudget.contextRowWeight rows)
    (fun _ => hP.context_row_weight_lower hp) (156 - 6 * S) hb hF h4
  rw [(hp.map (PrismBudget.contextRowWeight rows)).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hu
  unfold PrismBudget.contextUpper PrismBudget.contextPairSlack
  omega

end Kalai5
