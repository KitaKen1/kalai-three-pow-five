import Kalai5.Endpoints.UniversalRidge
import Kalai5.Endpoints.LargeGapCapacity

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def ridgePolygonOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide ((R.n = 8 ∧ R.r ≤ 8) →
    2 * R.p ≤ R.J + (negativeCarrierPairs S rows - 1))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Different polygon faces of a ridge need different other ridges inside
the containing facet. This is the lower bound complementary to the
near-pyramid upper bound. -/
theorem IsCSPolytope5.ridge_polygon_count_lower
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) :
    cnt P T 2 + 1 ≤ cnt P F 3 := by
  have hother : ∀ Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2},
      ∃ R ∈ {R | R ∈ faces P ∧ Q ⊆ R ∧ R ⊆ F ∧ dim R = 3}, R ≠ T := by
    intro Q hQ
    exact exists_ne_of_ncard_eq_two (hP.twoface_in_facet hF h4 hQ.1
      (hQ.2.1.trans hTF) hQ.2.2) ⟨hT,hQ.2.1,hTF,hT3⟩
  choose! f hf hfT using hother
  have hi : Set.InjOn f {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} := by
    intro Q hQ U hU he
    obtain ⟨hR,hQR,_,hR3⟩ := hf Q hQ
    obtain ⟨hS,hUS,_,hS3⟩ := hf U hU
    have hq := hP.inter_three_eq hQ.1 hQ.2.2 hT hT3 hR hR3 (hfT Q hQ).symm hQ.2.1 hQR
    have hu := hP.inter_three_eq hU.1 hU.2.2 hT hT3 hS hS3 (hfT U hU).symm hU.2.1 hUS
    exact hq.symm.trans ((congrArg (fun R => T ∩ R) he).trans hu)
  have hm : f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2} ⊆
      {R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3} \ {T} := by
    rintro R ⟨Q,hQ,rfl⟩
    obtain ⟨hR,_,hRF,hR3⟩ := hf Q hQ
    exact ⟨⟨hR,hRF,hR3⟩,hfT Q hQ⟩
  have hn : (f '' {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2}).ncard = cnt P T 2 :=
    hi.ncard_image
  have hb : ({R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3} \ {T}).ncard = cnt P F 3 - 1 :=
    Set.ncard_sdiff_singleton_of_mem ⟨hT,hTF,hT3⟩
  have hc := Set.ncard_le_ncard hm (hP.below_finite F 3).sdiff
  rw [hn,hb] at hc
  have hmem : ({T} : Set (Set E5)) ⊆ {R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3} := by
    rintro R rfl
    exact ⟨hT,hTF,hT3⟩
  have hpos := Set.ncard_le_ncard hmem (hP.below_finite F 3)
  rw [Set.ncard_singleton] at hpos
  change 1 ≤ cnt P F 3 at hpos
  omega

theorem IsCSPolytope5.tcnt_zero_of_polygon_count
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    {t : ℕ × ℕ × ℕ} (ht : cnt P F 3 ≤ t.2.2) : tcnt P F t = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,he⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
  have hp : cnt P T 2 = t.2.2 := congrArg (fun u => u.2.2) he
  have hc := hP.ridge_polygon_count_lower hF h4 hT hTF hT3
  omega

theorem IsCSPolytope5.large_gap_zero_of_at_most_eight_ridges
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hr : cnt P F 3 ≤ 8) :
    ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
  intro t ht
  have hc : ∀ t ∈ PrismBudget.largeGapTypes, 8 ≤ t.2.2 := by decide +kernel
  exact hP.tcnt_zero_of_polygon_count hF h4 (hr.trans (hc t ht))

theorem IsCSPolytope5.ridge_polygon_capacity_necessary {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S) :
    PrismBudget.ridgePolygonOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  apply decide_eq_true
  rintro ⟨hn,hr⟩
  by_cases hgap : R.J < 2 * R.p
  · obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
    have hFn : cnt P F 0 = 8 := (congrArg Row.n hR).trans hn
    have hFr : cnt P F 3 ≤ 8 := by change (faceRow P F).r ≤ 8; rwa [hR]
    have hFp : cnt P F 2 = R.p := congrArg Row.p hR
    have hFj : incid P F 0 3 = R.J := congrArg Row.J hR
    have hz := hP.large_gap_zero_of_at_most_eight_ridges hF h4 hFr
    have hlo := hP.negative_gap_count_lower_no_large hF h4 hFn hz
    have hnot := hP.negative_gap_demand_not_free_at hF h4
      (Or.inr ⟨hFn,by change incid P F 0 3 < 2 * cnt P F 2; omega⟩)
      (hP.facet_weight_le_of_qFour_pair_slack hp hb hF h4)
    have hcap := hP.negative_gap_ridge_capacity hp hb hF h4 hFn.le hnot
    omega
  · omega

end Kalai5

