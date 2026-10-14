import Kalai5.Endpoints.FullNineGeometry
import Kalai5.Endpoints.LargeGapCapacity
import Kalai5.Endpoints.ContextWeight

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def nineSmallLargeFree (S : ℤ) (rows : List Row) : Prop :=
  (rows.all fun R => decide (R.n = 8 ∨ largeGapFreeAt (qFourPairSlack S rows) R)) = true

instance (S : ℤ) (rows : List Row) : Decidable (nineSmallLargeFree S rows) := by
  unfold nineSmallLargeFree
  infer_instance

def nineCarrierPairs (S : ℤ) (rows : List Row) (R : Row) : ℕ :=
  (rows.filter fun U => decide (U = R ∨
    (U.n ≠ 8 ∧ ¬ negativeGapFreeAt (qFourPairSlack S rows) U))).length

def nineSupportOK (S : ℤ) (rows : List Row) : Bool :=
  rows.all fun R => decide ((R.n = 8 ∧ R.r = 9 ∧ nineSmallLargeFree S rows) →
    2 * R.p ≤ R.J + (nineCarrierPairs S rows R - 1))

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- If a large ridge type has no non-full carrier, it is absent from a
full nine-ridge facet. -/
theorem IsCSPolytope5.full_nine_type_zero_of_small_free
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 = 8) (hr : cnt P F 3 = 9)
    (t : ℕ × ℕ × ℕ) (ht5 : 5 ≤ t.1)
    (hsmall : ∀ H ∈ faces P, dim H = 4 → cnt P H 0 ≠ 8 → tcnt P H t = 0) :
    tcnt P F t = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
  have hTn : cnt P T 0 = t.1 := congrArg Prod.fst ht
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hHn := hP.full_nine_large_ridge_partner_nonfull hv hh ha hF h4 hn hr
    hT hTF hT3 (by omega) hH hH4 hHF hTH
  have hpos := hP.one_le_tcnt hT hTH hT3
  rw [ht,hsmall H hH hH4 hHn] at hpos
  omega

theorem IsCSPolytope5.full_nine_large_gap_counts_zero
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {rows : List Row} {S : ℤ} (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    (hs : PrismBudget.nineSmallLargeFree S rows)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 = 8) (hr : cnt P F 3 = 9) :
    ∀ t ∈ PrismBudget.largeGapTypes, tcnt P F t = 0 := by
  intro t ht
  have hc : ∀ t ∈ PrismBudget.largeGapTypes, 5 ≤ t.1 := by decide +kernel
  apply hP.full_nine_type_zero_of_small_free hv hh ha hF h4 hn hr t (hc t ht)
  intro H hH hH4 hHn
  have hm := hP.faceRow_mem_pair_rows hp hH hH4
  have hk := of_decide_eq_true ((List.all_eq_true.1 hs) _ hm)
  have hfree := hk.resolve_left hHn
  exact hP.large_gap_free_at_counts hH hH4 hfree
    (hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4) t ht

/-- Only non-full pairs can supply the negative-gap ridges of a full
nine-ridge facet; its own row pair is included for the existing capacity lemma. -/
theorem IsCSPolytope5.full_nine_negative_gap_capacity
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {rows : List Row} {S : ℤ} (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 = 8) (hr : cnt P F 3 = 9) :
    (PrismBudget.negativeGapTypes.map (tcnt P F)).sum + 1 ≤
      PrismBudget.nineCarrierPairs S rows (faceRow P F) := by
  let A := (hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ PrismBudget.negativeGapTypes
  let carrier : Row → Prop := fun U => U = faceRow P F ∨
    (U.n ≠ 8 ∧ ¬ PrismBudget.negativeGapFreeAt (PrismBudget.qFourPairSlack S rows) U)
  have hA : ∀ T ∈ A, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 := by
    intro T hT
    have hm := (Finset.mem_filter.1 hT).1
    rwa [Set.Finite.mem_toFinset] at hm
  have h5 : ∀ T ∈ A, 5 ≤ cnt P T 0 := by
    intro T hT
    have hc : ∀ t ∈ PrismBudget.negativeGapTypes, 5 ≤ t.1 := by decide +kernel
    exact hc _ (Finset.mem_filter.1 hT).2
  have hwide : ∀ T ∈ A, ∀ U ∈ A, cnt P F 0 < cnt P T 0 + cnt P U 0 := by
    intro T hT U hU
    have ht := h5 T hT
    have hu := h5 U hU
    omega
  have hcar : ∀ T ∈ A, ∀ H ∈ faces P, dim H = 4 → T ⊆ H → carrier (faceRow P H) := by
    intro T hTA H hH hH4 hTH
    by_cases he : H = F
    · subst H
      exact Or.inl rfl
    · have hnon := hP.full_nine_large_ridge_partner_nonfull hv hh ha hF h4 hn hr
        (hA T hTA).1 (hA T hTA).2.1 (hA T hTA).2.2 (h5 T hTA) hH hH4 he hTH
      refine Or.inr ⟨hnon,?_⟩
      intro hfree
      have hz := hP.negative_gap_free_at_counts hH hH4 hfree
        (hP.facet_weight_le_of_qFour_pair_slack hp hb hH hH4) _ (Finset.mem_filter.1 hTA).2
      have hpos := hP.one_le_tcnt (hA T hTA).1 hTH (hA T hTA).2.2
      omega
  have hc := hP.ridge_antipodal_capacity carrier hF h4 (Or.inl rfl) A hA hwide hcar
  have he := (hp.filter (fun R => decide (carrier R))).length_eq
  rw [List.filter_append,List.length_append] at he
  rw [he] at hc
  have hsum := hP.tcnt_list_sum_eq_card F PrismBudget.negativeGapTypes (by decide +kernel)
  change (PrismBudget.negativeGapTypes.map (tcnt P F)).sum = A.card at hsum
  change (PrismBudget.negativeGapTypes.map (tcnt P F)).sum + 1 ≤
    (rows.filter fun R => decide (carrier R)).length
  omega

theorem IsCSPolytope5.nine_support_necessary
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (ha : cnt8 (facetRows P) = 4)
    {rows : List Row} {S : ℤ} (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S) :
    PrismBudget.nineSupportOK S rows = true := by
  apply List.all_eq_true.2
  intro R hRm
  apply decide_eq_true
  rintro ⟨hn,hr,hs⟩
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hRm))
  have hFn : cnt P F 0 = 8 := (congrArg Row.n hR).trans hn
  have hFr : cnt P F 3 = 9 := (congrArg Row.r hR).trans hr
  have hz := hP.full_nine_large_gap_counts_zero hv hh ha hp hb hs hF h4 hFn hFr
  have hlo := hP.negative_gap_count_lower_no_large hF h4 hFn hz
  have hcap := hP.full_nine_negative_gap_capacity hv hh ha hp hb hF h4 hFn hFr
  have hFp : cnt P F 2 = R.p := congrArg Row.p hR
  have hFj : incid P F 0 3 = R.J := congrArg Row.J hR
  rw [hR] at hcap
  omega

end Kalai5

