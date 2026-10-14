import Kalai5.Endpoints.NegativeGapCapacity

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def largeGapTypes : List (ℕ × ℕ × ℕ) := [(6,12,8),(7,14,9),(7,15,10)]

def largeGapSmallFreeRows : List Row :=
  bipyrSmallFreeRows ++ [jRow,⟨7,17,18,8,35⟩]

def largeGapFreeAt (s : ℤ) (R : Row) : Prop :=
  negativeGapFreeAt s R ∨ R ∈ largeGapSmallFreeRows ∨ R = zRow ∨
    (R.n = 8 ∧ 8 ≤ R.r ∧
      ((2 * R.p ≤ R.J + 1 ∧ (rowExcess R < 3 ∨
        (q55QFourRowWeight R : ℤ) + s < prismLower R)) ∨
       (2 * R.p ≤ R.J ∧ rowExcess R ≤ 4)))

instance (s : ℤ) (R : Row) : Decidable (largeGapFreeAt s R) := by
  unfold largeGapFreeAt
  infer_instance

def largeGapCapacityOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide (R.n ≠ 8 ∨ pairRowCount R rows ≠ 1) ||
    !(rows.all fun U => decide (U = R ∨ largeGapFreeAt (qFourPairSlack S rows) U)) ||
    decide (2 * R.p ≤ R.J + (negativeCarrierPairs S rows - 1))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.large_gap_zero_of_event_bound {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (he : 2 * cnt P F 2 + tcnt P F (6,9,5) + tcnt P F (7,11,6) ≤ incid P F 0 3 + 1) :
    ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  intro t ht
  simp only [PrismBudget.largeGapTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> omega

theorem IsCSPolytope5.small_large_gap_counts_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.largeGapSmallFreeRows) :
    ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
  have hc : ∀ R ∈ PrismBudget.largeGapSmallFreeRows, R.n = 7 := by decide +kernel
  have hn : cnt P F 0 = 7 := hc _ hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.largeGapSmallFreeRows →
      X.2.1[6]? = some 0 := by decide +kernel
  have hz := hcheck _ hm (by change rowOf F ∈ _; rw [he]; exact hR)
  have hp := congrArg (fun xs : List ℕ => xs[6]?) (hP.facet_profile hF h4 hn.le).2
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hp
  rw [hz] at hp
  intro t ht
  simp only [PrismBudget.largeGapTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [hP.tcnt_eq_card]; exact (Option.some.inj hp).symm
  all_goals exact hP.small_facet_seven_ridge_zero hF h4 hn.le _ _

theorem IsCSPolytope5.large_gap_free_at_counts {F : Set E5} {s : ℤ}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.largeGapFreeAt s (faceRow P F))
    (hw : q55w P F + 2 * exc P F ≤ (q55QFourRowWeight (faceRow P F) : ℤ) + s) :
    ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
  rcases hR with hn | hs | hz | ⟨hn,hr,hcases⟩
  · have hc : ∀ t ∈ PrismBudget.largeGapTypes, t ∈ PrismBudget.negativeGapTypes := by decide +kernel
    exact fun t ht => hP.negative_gap_free_at_counts hF h4 hn hw t (hc t ht)
  · exact hP.small_large_gap_counts_zero hF h4 hs
  · have hn : cnt P F 0 = 8 := congrArg Row.n hz
    have hr : cnt P F 3 = 7 := congrArg Row.r hz
    obtain ⟨a,b,c,d,e,f⟩ := hP.r19_types hF h4 hz
    obtain ⟨c1,_,_,_⟩ := hP.facet8_arith hF h4 hn
    intro t ht
    simp only [PrismBudget.largeGapTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · have h7 := hP.eight_ridges_no_7116 hF h4 hn hr
    have he : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
    apply hP.large_gap_zero_of_event_bound hF h4 hn
    rcases hcases with ⟨hgap,hpr⟩ | ⟨hgap,he4⟩
    · change 2 * cnt P F 2 ≤ incid P F 0 3 + 1 at hgap
      have hp0 : tcnt P F (6,9,5) = 0 := by
        rcases hpr with he3 | hl
        · exact hP.tcnt_zero_of_exc_lt (by simp only; omega)
        · by_contra hz
          have hh := (hP.prism_weight_lower hF h4 hn (by omega)).2
          omega
      omega
    · change 2 * cnt P F 2 ≤ incid P F 0 3 at hgap
      have hp1 := hP.prism_count_le_one_of_exc_le_four (by omega : exc P F ≤ 4)
      omega

theorem IsCSPolytope5.negative_gap_count_lower_no_large {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (hz : ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0) :
    2 * cnt P F 2 ≤ incid P F 0 3 + (PrismBudget.negativeGapTypes.map (tcnt P F)).sum := by
  have ha := hz (6,12,8) (by simp [PrismBudget.largeGapTypes])
  have hb := hz (7,14,9) (by simp [PrismBudget.largeGapTypes])
  have hc := hz (7,15,10) (by simp [PrismBudget.largeGapTypes])
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [PrismBudget.negativeGapTypes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem IsCSPolytope5.large_gap_capacity_necessary {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤ 156 - 6 * S) :
    PrismBudget.largeGapCapacityOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  by_cases hn : R.n = 8
  · by_cases hcount : PrismBudget.pairRowCount R rows = 1
    · by_cases hall : ∀ U ∈ rows, U = R ∨ PrismBudget.largeGapFreeAt (PrismBudget.qFourPairSlack S rows) U
      · have hineq : 2 * R.p ≤ R.J + (PrismBudget.negativeCarrierPairs S rows - 1) := by
          by_cases hgap : R.J < 2 * R.p
          · obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
            have hFn : cnt P F 0 = 8 := (congrArg Row.n hR).trans hn
            have hFp := congrArg Row.p hR
            have hFj := congrArg Row.J hR
            change cnt P F 2 = R.p at hFp
            change incid P F 0 3 = R.J at hFj
            have hnot := hP.negative_gap_demand_not_free_at hF h4
              (Or.inr ⟨hFn,by change incid P F 0 3 < 2 * cnt P F 2; omega⟩)
              (hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4)
            have hcap := hP.negative_gap_ridge_capacity hp hb hF h4 hFn.le hnot
            have hz : ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
              intro t ht
              apply hP.tcnt_zero_of_unique_pair_row hp hcount t (fun H hH hH4 hne => ?_) hF h4
              have hmH : faceRow P H ∈ rows := by
                have hmem : faceRow P H ∈ facetRows P := by
                  rw [hP.facetRows_eq]
                  exact List.mem_map.2 ⟨H,Finset.mem_toList.2 (by
                    rw [Set.Finite.mem_toFinset]; exact ⟨hH,hH4⟩),rfl⟩
                simpa only [List.mem_append,or_self] using hp.mem_iff.1 hmem
              exact hP.large_gap_free_at_counts hH hH4 ((hall _ hmH).resolve_left hne)
                (hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4) t ht
            have hl := hP.negative_gap_count_lower_no_large hF h4 hFn hz
            omega
          · omega
        simp [hineq]
      · have hf : (rows.all fun U => decide (U = R ∨ PrismBudget.largeGapFreeAt (PrismBudget.qFourPairSlack S rows) U)) = false := by
          apply Bool.eq_false_iff.2
          intro hh
          exact hall (fun U hU => of_decide_eq_true ((List.all_eq_true.1 hh) U hU))
        simp only [hf,Bool.not_false,Bool.or_true,Bool.true_or]
    · simp [hcount]
  · simp [hn]

end Kalai5
