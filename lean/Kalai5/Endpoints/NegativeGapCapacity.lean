import Kalai5.Endpoints.AntipodalRidgeCapacity
import Kalai5.Endpoints.QFourPairBudget

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def negativeGapFreeAt (slack : ℤ) (R : Row) : Prop :=
  negativeGapFree R ∨ (R.n = 8 ∧ 8 ≤ R.r ∧ 2 * R.p ≤ R.J ∧
    (q55QFourRowWeight R : ℤ) + slack < prismLower R)

instance (slack : ℤ) (R : Row) : Decidable (negativeGapFreeAt slack R) := by
  unfold negativeGapFreeAt
  infer_instance

def negativeCarrierPairs (S : ℤ) (rows : List Row) : ℕ :=
  (rows.filter fun R => decide (¬ negativeGapFreeAt (qFourPairSlack S rows) R)).length

def negativeGapCoefficient (S : ℤ) (rows : List Row) (R : Row) : ℕ :=
  if (q55QFourRowWeight R : ℤ) + qFourPairSlack S rows < 2 * rowExcess R then 2 else 3

def negativeCapacityOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide
    ((R = jRow → 3 ≤ negativeCarrierPairs S rows) ∧
      (R.n = 8 → 2 * R.p ≤ R.J + negativeGapCoefficient S rows R *
        (negativeCarrierPairs S rows - 1)))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.negative_gap_count_lower {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8) :
    2 * cnt P F 2 ≤ incid P F 0 3 +
      3 * (PrismBudget.negativeGapTypes.map (tcnt P F)).sum := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [PrismBudget.negativeGapTypes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem IsCSPolytope5.negative_gap_count_lower_no_seven {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (h7 : tcnt P F (7,15,10) = 0) :
    2 * cnt P F 2 ≤ incid P F 0 3 +
      2 * (PrismBudget.negativeGapTypes.map (tcnt P F)).sum := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [PrismBudget.negativeGapTypes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem IsCSPolytope5.j_negative_gap_count_two {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = PrismBudget.jRow) :
    2 ≤ (PrismBudget.negativeGapTypes.map (tcnt P F)).sum := by
  have ht := hP.small_bipyr_marked_count hF h4 (Or.inl hR)
  rw [if_pos hR] at ht
  simp only [PrismBudget.negativeGapTypes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem IsCSPolytope5.negative_gap_demand_not_free {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hd : PrismBudget.negativeGapDemand (faceRow P F)) :
    ¬ PrismBudget.negativeGapFree (faceRow P F) := by
  intro hf
  obtain ⟨t,ht,hpos⟩ := hP.negative_gap_demand_positive hF h4 hd
  have hz := hP.negative_gap_free_counts hF h4 hf t ht
  omega

theorem IsCSPolytope5.negative_gap_free_at_counts {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.negativeGapFreeAt s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + s) :
    ∀ t ∈ PrismBudget.negativeGapTypes, tcnt P F t = 0 := by
  rcases hR with hfree | ⟨hn,hr,hgap,hlow⟩
  · exact hP.negative_gap_free_counts hF h4 hfree
  · have h7 := hP.eight_ridges_no_7116 hF h4 hn hr
    have hpr : tcnt P F (6,9,5) = 0 := by
      by_contra hz
      have hl := (hP.prism_weight_lower hF h4 hn (by omega)).2
      omega
    change 2 * cnt P F 2 ≤ incid P F 0 3 at hgap
    exact hP.negative_gap_ridges_zero_of_event_bound hF h4 hn (by omega)

theorem IsCSPolytope5.negative_gap_demand_not_free_at {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hd : PrismBudget.negativeGapDemand (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + s) :
    ¬ PrismBudget.negativeGapFreeAt s (faceRow P F) := by
  intro hf
  obtain ⟨t,ht,hpos⟩ := hP.negative_gap_demand_positive hF h4 hd
  have hz := hP.negative_gap_free_at_counts hF h4 hf hw t ht
  omega

/-- Each negative-gap ridge occupies a different carrier pair. -/
theorem IsCSPolytope5.negative_gap_ridge_capacity {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 8)
    (hcar : ¬ PrismBudget.negativeGapFreeAt (PrismBudget.qFourPairSlack S rows) (faceRow P F)) :
    (PrismBudget.negativeGapTypes.map (tcnt P F)).sum + 1 ≤
      PrismBudget.negativeCarrierPairs S rows := by
  apply hP.ridge_type_pair_capacity (fun R => ¬ PrismBudget.negativeGapFreeAt (PrismBudget.qFourPairSlack S rows) R)
    PrismBudget.negativeGapTypes (by decide +kernel) hp
    (fun H hH hH4 hn => hP.negative_gap_free_at_counts hH hH4 (not_not.1 hn)
      (hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4)) hF h4 hcar
  intro t ht u hu
  have hc : ∀ v ∈ PrismBudget.negativeGapTypes, 5 ≤ v.1 := by decide +kernel
  have h1 := hc t ht
  have h2 := hc u hu
  omega

theorem IsCSPolytope5.negative_gap_capacity_necessary {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.negativeCapacityOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRmem
  apply decide_eq_true
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRmem))
  have hupper := hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4
  constructor
  · intro hj
    have hFj : faceRow P F = PrismBudget.jRow := hR.trans hj
    have hFn : cnt P F 0 = 7 := congrArg Row.n hFj
    have hnot := hP.negative_gap_demand_not_free_at hF h4 (Or.inl hFj) hupper
    have hc := hP.negative_gap_ridge_capacity hp hb hF h4 (by omega) hnot
    have hl := hP.j_negative_gap_count_two hF h4 hFj
    omega
  · intro hn
    by_cases hgap : R.J < 2 * R.p
    · have hFn : cnt P F 0 = 8 := (congrArg Row.n hR).trans hn
      have hFp := congrArg Row.p hR
      have hFj := congrArg Row.J hR
      change cnt P F 2 = R.p at hFp
      change incid P F 0 3 = R.J at hFj
      have hnot := hP.negative_gap_demand_not_free_at hF h4
        (Or.inr ⟨hFn,by change incid P F 0 3 < 2 * cnt P F 2; omega⟩) hupper
      have hc := hP.negative_gap_ridge_capacity hp hb hF h4 hFn.le hnot
      unfold PrismBudget.negativeGapCoefficient
      split_ifs with hlow
      · have hw := hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4
        have he : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
        rw [hR] at hw he
        have h7 := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hFn (by omega) 15 10
        have hl := hP.negative_gap_count_lower_no_seven hF h4 hFn h7
        omega
      · have hl := hP.negative_gap_count_lower hF h4 hFn
        omega
    · have hnonneg : 0 ≤ PrismBudget.negativeGapCoefficient S rows R *
          (PrismBudget.negativeCarrierPairs S rows - 1) := Nat.zero_le _
      omega

end Kalai5
