import Kalai5.Endpoints.RidgeExcess
import Kalai5.Endpoints.SinglePairSupport

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

/-- The six ridge types having more faces than vertices. -/
def negativeGapTypes : List (ℕ × ℕ × ℕ) :=
  [(5,9,6),(6,11,7),(6,12,8),(7,13,8),(7,14,9),(7,15,10)]

def negativeGapFree (R : Row) : Prop :=
  R ∈ bipyrSmallFreeRows ∨ R = r35Row ∨ R = r0Row ∨ R ∈ exactPrismRows ∨
    (R.n = 8 ∧ 8 ≤ R.r ∧ 2 * R.p ≤ R.J ∧ rowExcess R < 3)

def negativeGapDemand (R : Row) : Prop :=
  R = jRow ∨ (R.n = 8 ∧ R.J < 2 * R.p)

instance (R : Row) : Decidable (negativeGapFree R) := by
  unfold negativeGapFree
  infer_instance

instance (R : Row) : Decidable (negativeGapDemand R) := by
  unfold negativeGapDemand
  infer_instance

def negativeGapSupportOK (rows : List Row) : Bool :=
  rows.all fun R => !decide (negativeGapDemand R) ||
    singleSupportOK R (rows.filter fun S => decide (negativeGapFree S)) rows

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The positive gap is supplied only by prisms and (7,11,6) ridges.
If it exhausts the flag gap, every negative-gap ridge count vanishes. -/
theorem IsCSPolytope5.negative_gap_ridges_zero_of_event_bound {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (he : 2 * cnt P F 2 + tcnt P F (6,9,5) + tcnt P F (7,11,6) ≤ incid P F 0 3) :
    ∀ t ∈ PrismBudget.negativeGapTypes, tcnt P F t = 0 := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  intro t ht
  simp only [PrismBudget.negativeGapTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem IsCSPolytope5.negative_gap_ridge_of_flag_gap {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8)
    (he : incid P F 0 3 < 2 * cnt P F 2) :
    ∃ t ∈ PrismBudget.negativeGapTypes, 1 ≤ tcnt P F t := by
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  by_contra hbad
  have hz : ∀ t ∈ PrismBudget.negativeGapTypes, tcnt P F t = 0 := by
    intro t ht
    have hh : ¬ 1 ≤ tcnt P F t := fun hp => hbad ⟨t,ht,hp⟩
    omega
  have ha := hz (5,9,6) (by simp [PrismBudget.negativeGapTypes])
  have hb := hz (6,11,7) (by simp [PrismBudget.negativeGapTypes])
  have hc := hz (6,12,8) (by simp [PrismBudget.negativeGapTypes])
  have hd := hz (7,13,8) (by simp [PrismBudget.negativeGapTypes])
  have hf := hz (7,14,9) (by simp [PrismBudget.negativeGapTypes])
  have hg := hz (7,15,10) (by simp [PrismBudget.negativeGapTypes])
  omega

theorem IsCSPolytope5.small_negative_gap_ridges_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.bipyrSmallFreeRows) :
    ∀ t ∈ PrismBudget.negativeGapTypes, tcnt P F t = 0 := by
  have hc : ∀ R ∈ PrismBudget.bipyrSmallFreeRows, R.n = 7 := by decide +kernel
  have hn : cnt P F 0 = 7 := hc _ hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.bipyrSmallFreeRows →
      X.2.1[2]? = some 0 ∧ X.2.1[5]? = some 0 ∧ X.2.1[6]? = some 0 := by
    decide +kernel
  obtain ⟨h2,h5,h6⟩ := hcheck _ hm (by change rowOf F ∈ _; rw [he]; exact hR)
  have hp := (hP.facet_profile hF h4 hn.le).2
  have hp2 := congrArg (fun xs : List ℕ => xs[2]?) hp
  have hp5 := congrArg (fun xs : List ℕ => xs[5]?) hp
  have hp6 := congrArg (fun xs : List ℕ => xs[6]?) hp
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero]
    at hp2 hp5 hp6
  rw [h2] at hp2
  rw [h5] at hp5
  rw [h6] at hp6
  intro t ht
  simp only [PrismBudget.negativeGapTypes,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hP.tcnt_eq_card]; exact (Option.some.inj hp2).symm
  · rw [hP.tcnt_eq_card]; exact (Option.some.inj hp5).symm
  · rw [hP.tcnt_eq_card]; exact (Option.some.inj hp6).symm
  all_goals exact hP.small_facet_seven_ridge_zero hF h4 hn.le _ _

theorem IsCSPolytope5.negative_gap_free_counts {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.negativeGapFree (faceRow P F)) :
    ∀ t ∈ PrismBudget.negativeGapTypes, tcnt P F t = 0 := by
  rcases hR with hs | h35 | h0 | hx | ⟨hn,hr,hgap,he⟩
  · exact hP.small_negative_gap_ridges_zero hF h4 hs
  · have hn : cnt P F 0 = 8 := congrArg Row.n h35
    have hp : cnt P F 2 = 17 := congrArg Row.p h35
    have hj : incid P F 0 3 = 35 := congrArg Row.J h35
    have hh := hP.r35_event_one hF h4 h35
    exact hP.negative_gap_ridges_zero_of_event_bound hF h4 hn (by omega)
  · have hn : cnt P F 0 = 8 := congrArg Row.n h0
    have hp : cnt P F 2 = 17 := congrArg Row.p h0
    have hj : incid P F 0 3 = 36 := congrArg Row.J h0
    obtain ⟨a,b,c,d,e,f⟩ := hP.r0_types hF h4 h0
    exact hP.negative_gap_ridges_zero_of_event_bound hF h4 hn (by omega)
  · have hc : ∀ R ∈ PrismBudget.exactPrismRows, R.n = 8 ∧ R.J = 2 * R.p + 1 := by
      decide +kernel
    obtain ⟨hn,hgap⟩ := hc _ hx
    have he := hP.exact_prism_event_count hF h4 hx
    change incid P F 0 3 = 2 * cnt P F 2 + 1 at hgap
    exact hP.negative_gap_ridges_zero_of_event_bound hF h4 hn (by omega)
  · have h7 := hP.eight_ridges_no_7116 hF h4 hn hr
    have heq : exc P F = PrismBudget.rowExcess (faceRow P F) := hP.exc_eq_faceRow hF h4
    have hpr : tcnt P F (6,9,5) = 0 := hP.tcnt_zero_of_exc_lt (by simp only; omega)
    change 2 * cnt P F 2 ≤ incid P F 0 3 at hgap
    exact hP.negative_gap_ridges_zero_of_event_bound hF h4 hn (by omega)

theorem IsCSPolytope5.negative_gap_demand_positive {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : PrismBudget.negativeGapDemand (faceRow P F)) :
    ∃ t ∈ PrismBudget.negativeGapTypes, 1 ≤ tcnt P F t := by
  rcases hR with hj | ⟨hn,hgap⟩
  · have ht := hP.small_bipyr_marked_count hF h4 (Or.inl hj)
    rw [if_pos hj] at ht
    exact ⟨(5,9,6),by simp [PrismBudget.negativeGapTypes],by omega⟩
  · exact hP.negative_gap_ridge_of_flag_gap hF h4 hn hgap

/-- A demanded negative gap cannot be carried by only one antipodal row pair. -/
theorem IsCSPolytope5.negative_gap_pair_support {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) :
    PrismBudget.negativeGapSupportOK rows = true := by
  apply List.all_eq_true.2
  intro R _
  by_cases hd : PrismBudget.negativeGapDemand R
  · have hs : PrismBudget.singleSupportOK R
        (rows.filter fun S => decide (PrismBudget.negativeGapFree S)) rows = true := by
      apply hP.single_pair_support_necessary _ _ PrismBudget.negativeGapTypes hp
      · intro F hF h4 hR
        exact hP.negative_gap_demand_positive hF h4 (by simpa only [hR] using hd)
      · intro F hF h4 hR
        exact hP.negative_gap_free_counts hF h4 (of_decide_eq_true (List.mem_filter.1 hR).2)
    simp [hd,hs]
  · simp [hd]

end Kalai5
