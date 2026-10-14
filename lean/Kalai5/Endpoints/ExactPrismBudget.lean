import Kalai5.Endpoints.ExactPrismCount

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

/-- Any known row count whose geometric total is a multiple of four
must have an even sum on the antipodal pair rows. -/
def rowParityOK (value : Row → ℕ) (known : Row → Bool) (rows : List Row) : Bool :=
  decide (2 ∣ (rows.map value).sum) || !(rows.all known)

def exactPrismParityOK (S : ℤ) (rows : List Row) : Bool :=
  rowParityOK exactPrismValue (fun R => decide (exactPrismKnown (pairSlack S rows) R)) rows

def exactEventParityOK (S : ℤ) (rows : List Row) : Bool :=
  rowParityOK exactRowEvent (fun R => decide (exactEventKnown (pairSlack S rows) R)) rows

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A generic bridge from four-divisible geometric counts to a one-bit
finite row filter. The predicate may incorporate a certified local budget. -/
theorem IsCSPolytope5.facet_count_pair_row_parity
    (count : Set E5 → ℕ) (value : Row → ℕ) (known : Row → Bool) {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hlocal : ∀ F ∈ faces P, dim F = 4 → known (faceRow P F) = true →
      count F = value (faceRow P F))
    (hdiv : 4 ∣ ∑ F ∈ (hP.kfaces_finite 4).toFinset, count F) :
    PrismBudget.rowParityOK value known rows = true := by
  by_cases heven : 2 ∣ (rows.map value).sum
  · simp [PrismBudget.rowParityOK,heven]
  by_cases hall : ∀ R ∈ rows, known R = true
  · have hcount : ∀ F ∈ (hP.kfaces_finite 4).toFinset, count F = value (faceRow P F) := by
      intro F hF
      have hFm := hF
      rw [Set.Finite.mem_toFinset] at hFm
      have hm : faceRow P F ∈ rows := by
        have hf : faceRow P F ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨F,Finset.mem_toList.2 hF,rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hf
      exact hlocal F hFm.1 hFm.2 (hall _ hm)
    have hs : (∑ F ∈ (hP.kfaces_finite 4).toFinset, count F) = 2 * (rows.map value).sum := by
      rw [Finset.sum_congr rfl hcount,← hP.facetRows_sum value,(hp.map _).sum_eq,
        List.map_append,List.sum_append]
      omega
    rw [hs] at hdiv
    omega
  · have hf : rows.all known = false := by
      apply Bool.eq_false_iff.2
      intro hh
      exact hall (List.all_eq_true.1 hh)
    simp only [PrismBudget.rowParityOK,hf,Bool.not_false,Bool.or_true]

theorem IsCSPolytope5.exact_prism_pair_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.exactPrismParityOK S rows = true := by
  apply hP.facet_count_pair_row_parity (fun F => tcnt P F (6,9,5))
    PrismBudget.exactPrismValue _ hp
  · intro F hF h4 hk
    exact hP.exact_prism_count_of_budget hF h4 (of_decide_eq_true hk)
      (hP.facet_weight_le_of_pair_slack hp hb hF h4)
  · exact hP.four_dvd_sum_tcnt (6,9,5)

theorem IsCSPolytope5.exact_event_pair_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.exactEventParityOK S rows = true := by
  apply hP.facet_count_pair_row_parity (fun F => tcnt P F (6,9,5) + tcnt P F (7,11,6))
    PrismBudget.exactRowEvent _ hp
  · intro F hF h4 hk
    exact hP.exact_event_count_of_budget hF h4 (of_decide_eq_true hk)
      (hP.facet_weight_le_of_pair_slack hp hb hF h4)
  · have hd := dvd_add (hP.four_dvd_sum_tcnt (6,9,5)) (hP.four_dvd_sum_tcnt (7,11,6))
    simpa only [Finset.sum_add_distrib] using hd

end Kalai5
