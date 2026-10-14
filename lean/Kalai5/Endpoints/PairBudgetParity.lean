import Kalai5.Endpoints.AntipodalWeightBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The Boolean parity filter is necessary for every geometric pair profile.
Its single parity bit is justified by the four-divisibility of ridge incidences. -/
theorem IsCSPolytope5.prism_pair_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.pairParityOK S rows = true := by
  by_cases heven : 2 ∣ PrismBudget.yCount rows
  · simp [PrismBudget.pairParityOK,heven]
  by_cases hall : ∀ R ∈ rows, R = excRow ∨ PrismBudget.freeAt (PrismBudget.pairSlack S rows) R
  · have hcount : ∀ F ∈ (hP.kfaces_finite 4).toFinset,
        tcnt P F (6,9,5) = if faceRow P F = excRow then 1 else 0 := by
      intro F hF
      have hFm := hF
      rw [Set.Finite.mem_toFinset] at hFm
      have hm : faceRow P F ∈ rows := by
        have hf : faceRow P F ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨F,Finset.mem_toList.2 hF,rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hf
      by_cases hY : faceRow P F = excRow
      · simp only [hY,ite_true]
        exact hP.Y_prism_count hFm.1 hFm.2 hY
      · rw [if_neg hY]
        apply hP.prism_free_of_budget hFm.1 hFm.2 ((hall _ hm).resolve_left hY)
        exact hP.facet_weight_le_of_pair_slack hp hb hFm.1 hFm.2
    have hs : (∑ F ∈ (hP.kfaces_finite 4).toFinset, tcnt P F (6,9,5)) =
        2 * PrismBudget.yCount rows := by
      rw [Finset.sum_congr rfl hcount,← hP.facetRows_sum (fun R => if R = excRow then 1 else 0),(hp.map _).sum_eq,
        List.map_append,List.sum_append]
      unfold PrismBudget.yCount
      omega
    have hd := hP.four_dvd_sum_tcnt (6,9,5)
    rw [hs] at hd
    omega
  · have hf : (rows.all fun R => decide (R = excRow ∨
        PrismBudget.freeAt (PrismBudget.pairSlack S rows) R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      apply hall
      intro R hR
      exact of_decide_eq_true ((List.all_eq_true.1 hh) R hR)
    simp only [PrismBudget.pairParityOK,hf,Bool.not_false,Bool.or_true]


/-- A second parity check adds the (7,11,6) count to the prism count. -/
theorem IsCSPolytope5.event_pair_budget_parity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.pairEventParityOK S rows = true := by
  by_cases heven : 2 ∣ (rows.map PrismBudget.rowEvent).sum
  · simp [PrismBudget.pairEventParityOK,heven]
  by_cases hall : ∀ R ∈ rows, PrismBudget.eventKnown (PrismBudget.pairSlack S rows) R
  · have hcount : ∀ F ∈ (hP.kfaces_finite 4).toFinset,
        tcnt P F (6,9,5) + tcnt P F (7,11,6) = PrismBudget.rowEvent (faceRow P F) := by
      intro F hF
      have hFm := hF
      rw [Set.Finite.mem_toFinset] at hFm
      have hm : faceRow P F ∈ rows := by
        have hf : faceRow P F ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨F,Finset.mem_toList.2 hF,rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hf
      apply hP.event_count_of_budget hFm.1 hFm.2 (hall _ hm)
      exact hP.facet_weight_le_of_pair_slack hp hb hFm.1 hFm.2
    have hs : (∑ F ∈ (hP.kfaces_finite 4).toFinset,
        (tcnt P F (6,9,5) + tcnt P F (7,11,6))) = 2 * (rows.map PrismBudget.rowEvent).sum := by
      rw [Finset.sum_congr rfl hcount,← hP.facetRows_sum PrismBudget.rowEvent,(hp.map _).sum_eq,
        List.map_append,List.sum_append]
      omega
    have hd := dvd_add (hP.four_dvd_sum_tcnt (6,9,5)) (hP.four_dvd_sum_tcnt (7,11,6))
    rw [← Finset.sum_add_distrib,hs] at hd
    omega
  · have hf : (rows.all fun R => decide (PrismBudget.eventKnown (PrismBudget.pairSlack S rows) R)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      apply hall
      intro R hR
      exact of_decide_eq_true ((List.all_eq_true.1 hh) R hR)
    simp only [PrismBudget.pairEventParityOK,hf,Bool.not_false,Bool.or_true]


end Kalai5
