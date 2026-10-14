import Kalai5.Endpoints.E18positive.Globals
import Kalai5.Endpoints.TwoPairPositiveCatalogue
import Kalai5.Cert.PairedRows

/-! The positive-cell geometry compressed to nine certified antipodal row pairs. -/
namespace Kalai5
open scoped Classical

namespace TwoPairPositiveProfile

def ridgeExcess (R : Row) : ℕ := R.r - (R.n - 1)

lemma ridge_budget_identity (l : List Row) (hs : ∀ R ∈ l, R ∈ catalogue) :
    (l.map Row.r).sum + l.length =
      (l.map Row.n).sum + (l.map ridgeExcess).sum := by
  have hrow : ∀ R ∈ catalogue, R.r + 1 = R.n + ridgeExcess R := by decide +kernel
  induction l with
  | nil => simp
  | cons R rs ih =>
    have hR := hrow R (hs R (List.mem_cons_self ..))
    have ht := ih (fun S hS => hs S (List.mem_cons_of_mem R hS))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

end TwoPairPositiveProfile

noncomputable def positivePairRows (P : Set E5) : List Row :=
  cataloguePairs (facetRows P) TwoPairPositiveProfile.catalogue

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_catalogue
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    ∀ R ∈ facetRows P, R ∈ TwoPairPositiveProfile.catalogue := by
  obtain ⟨hc,_,_,_,hg,_⟩ := hP.fewFull18_positive_constraints hv hh h1 h6 hlt
  exact hP.two_pair_positive_catalogue hv hh hc
    (fun h => (not_le_of_gt hlt) (hP.full_prism hv h))
    (hP.fewFull18_positive_rows_ge_seven hv hh h1 h6 hlt) hg

/-- Doubling the compressed list recovers exactly the original row multiset. -/
theorem IsCSPolytope5.fewFull18_positive_pairs_perm
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (facetRows P).Perm (positivePairRows P ++ positivePairRows P) := by
  apply perm_double_cataloguePairs _ _ TwoPairPositiveProfile.catalogue_nodup
    (hP.fewFull18_positive_catalogue hv hh h1 h6 hlt)
  intro R
  simpa only [List.count_eq_length_filter] using hP.facetRows_filter_even (fun S => S == R)

/-- All integer budgets used by the nine-pair search follow from the actual geometry. -/
theorem IsCSPolytope5.fewFull18_positive_pair_budgets
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (positivePairRows P).length = 9 ∧
    cnt8 (positivePairRows P) = 2 ∧
    ((positivePairRows P).map Row.n).sum = 65 ∧
    ((positivePairRows P).map Row.r).sum = 60 ∧
    2 * (((positivePairRows P).map Row.e).sum : ℤ) = 288 + (flagDataOf P).Gs ∧
    ((positivePairRows P).map Row.g).sum = (flagDataOf P).G - 1 ∧
    2 * (((positivePairRows P).map q55BSixRowWeight).sum : ℤ) ≤
      156 - 6 * (flagDataOf P).Gs ∧
    ((positivePairRows P).map TwoPairPositiveProfile.ridgeExcess).sum = 4 := by
  have hs := hP.fewFull18_positive_catalogue hv hh h1 h6 hlt
  have hn := TwoPairPositiveProfile.catalogue_nodup
  have hev : ∀ R, Even ((facetRows P).count R) := by
    intro R
    simpa only [List.count_eq_length_filter] using hP.facetRows_filter_even (fun S => S == R)
  have hsum := fun f : Row → ℕ =>
    cataloguePairs_sum_nat (facetRows P) TwoPairPositiveProfile.catalogue hn hs hev f
  have hperm := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  have hlen0 := hperm.length_eq
  rw [hP.facetRows_length,hh,List.length_append] at hlen0
  have hlen : (positivePairRows P).length = 9 := by omega
  have hc0 := (hperm.filter (fun R => decide (R.n = 8))).length_eq
  simp only [List.filter_append,List.length_append] at hc0
  change cnt8 (facetRows P) = cnt8 (positivePairRows P) + cnt8 (positivePairRows P) at hc0
  have hc := (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
  have hc2 : cnt8 (positivePairRows P) = 2 := by omega
  obtain ⟨he,hp,hr,hi,_⟩ := hP.fewFull18_positive_face_numbers hv hh h1 h6 hlt
  have hnr := hsum Row.n
  rw [hP.facetRows_sum_n,show flag2 P 0 4 = 130 from hi] at hnr
  change 130 = 2 * ((positivePairRows P).map Row.n).sum at hnr
  have hn65 : ((positivePairRows P).map Row.n).sum = 65 := by omega
  have hrr := hsum Row.r
  rw [hP.facetRows_sum_r,hr] at hrr
  change 2 * 60 = 2 * ((positivePairRows P).map Row.r).sum at hrr
  have hr60 : ((positivePairRows P).map Row.r).sum = 60 := by omega
  have h14 : (((facetRows P).map Row.e).sum : ℤ) = 288 + (flagDataOf P).Gs := by
    rw [hP.facetRows_sum_e]
    change ((flagDataOf P).f14 : ℤ) = _
    rw [hP.flagData_valid.f14_eq]
    have hpD : (flagDataOf P).p = 86 := hp
    have hrD : (flagDataOf P).r = 60 := hr
    have hhD : (flagDataOf P).h = 18 := hh
    simp only [FlagData.Gs,hpD,hrD,hhD,hi]
    norm_num
    ring
  have her : 2 * (((positivePairRows P).map Row.e).sum : ℤ) = 288 + (flagDataOf P).Gs := by
    have ht := hsum Row.e
    change ((facetRows P).map Row.e).sum = 2 * ((positivePairRows P).map Row.e).sum at ht
    rw [ht] at h14
    exact_mod_cast h14
  have hgr := cataloguePairs_sum_int (facetRows P) TwoPairPositiveProfile.catalogue hn hs hev Row.g
  have hg0 := hP.facet_stress_sum_16_18 hv hh
  rw [hi] at hg0
  change ((facetRows P).map Row.g).sum = 2 * ((positivePairRows P).map Row.g).sum at hgr
  have hg : ((positivePairRows P).map Row.g).sum = (flagDataOf P).G - 1 := by omega
  have hwr := hsum q55BSixRowWeight
  change ((facetRows P).map q55BSixRowWeight).sum =
    2 * ((positivePairRows P).map q55BSixRowWeight).sum at hwr
  have hw := hP.fewFull18_positive_bSix_weight_budget hv hh h1 h6 hlt
  rw [hwr] at hw
  have hw' : 2 * (((positivePairRows P).map q55BSixRowWeight).sum : ℤ) ≤
      156 - 6 * (flagDataOf P).Gs := by exact_mod_cast hw
  have hx := TwoPairPositiveProfile.ridge_budget_identity (positivePairRows P)
    (cataloguePairs_support _ _)
  rw [hlen,hn65,hr60] at hx
  exact ⟨hlen,hc2,hn65,hr60,her,hg,hw',by omega⟩

end Kalai5
