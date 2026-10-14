import Kalai5.Endpoints.TwoPairPositiveG4S4

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- At the minimum V weight, the unique positive vertex-minus-face ridge
has seven vertices. -/
theorem IsCSPolytope5.v_weight_eight_seven_one
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,19,19,8,39⟩)
    (hW : q55w P F + 2 * exc P F ≤ 8) :
    tcnt P F (7,11,6) = 1 := by
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  have hp : tcnt P F (6,9,5) = 0 := by
    by_contra hz
    have ht := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6,9,5))
    omega
  have ht := hP.v_weight_ten_event_one hF h4 hR (by omega)
  omega

omit hP in
def g4s2ExcludedPairs : List Row :=
  [excRow,excRow,excRow,excRow,excRow,⟨7,16,16,7,32⟩,
   ⟨7,17,18,8,36⟩,⟨8,18,17,7,36⟩,⟨8,19,19,8,39⟩]

theorem IsCSPolytope5.two_pair_g4s2_excluded_weight_upper
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 2)
    (hprof : (facetRows P).Perm (g4s2ExcludedPairs ++ g4s2ExcludedPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (q55BSixRowWeight (faceRow P F) : ℤ) := by
  have hsum : (((facetRows P).map q55BSixRowWeight).sum : ℤ) = 144 := by
    rw [(hprof.map q55BSixRowWeight).sum_eq]
    decide +kernel
  have hu := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hu
  norm_num at hu
  simpa using hP.facet_weight_le_of_row_sum 144 144 hu hsum hF h4

theorem IsCSPolytope5.two_pair_g4s2_excluded_profile_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 2)
    (hprof : (facetRows P).Perm (g4s2ExcludedPairs ++ g4s2ExcludedPairs)) : False := by
  let eventCount : Row → ℕ := fun R => if R = ⟨8,19,19,8,39⟩ then 1 else 0
  have hs : ((facetRows P).map eventCount).sum = 2 := by
    rw [(hprof.map eventCount).sum_eq]
    decide +kernel
  rw [hP.facetRows_sum eventCount] at hs
  have heq : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      tcnt P H (7,11,6) = eventCount (faceRow P H) := by
    intro H hH
    have hHP := hH
    rw [Set.Finite.mem_toFinset] at hHP
    have hm : faceRow P H ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨H,Finset.mem_toList.2 hH,rfl⟩
    have hm' := hprof.mem_iff.1 hm
    have hcases : faceRow P H = excRow ∨ faceRow P H = ⟨7,16,16,7,32⟩ ∨
        faceRow P H = ⟨7,17,18,8,36⟩ ∨ faceRow P H = r0Row ∨
        faceRow P H = ⟨8,19,19,8,39⟩ := by
      simpa only [g4s2ExcludedPairs,r0Row,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,or_self,or_self_left,or_assoc] using hm'
    rcases hcases with hY | hZ | hR | hD | hV
    · have hn : cnt P H 0 = 7 := congrArg Row.n hY
      rw [hP.small_facet_seven_ridge_zero hHP.1 hHP.2 hn.le 11 6]
      simp [eventCount,hY,excRow]
    · have hn : cnt P H 0 = 7 := congrArg Row.n hZ
      rw [hP.small_facet_seven_ridge_zero hHP.1 hHP.2 hn.le 11 6]
      simp [eventCount,hZ]
    · have hn : cnt P H 0 = 7 := congrArg Row.n hR
      rw [hP.small_facet_seven_ridge_zero hHP.1 hHP.2 hn.le 11 6]
      simp [eventCount,hR]
    · rw [(hP.r0_types hHP.1 hHP.2 hD).2.2.2.2.2]
      simp [eventCount,hD,r0Row]
    · have hw := hP.two_pair_g4s2_excluded_weight_upper hv hh h1 h6 hlt hS hprof hHP.1 hHP.2
      rw [hV] at hw
      have hwV : q55BSixRowWeight (⟨8,19,19,8,39⟩ : Row) = 8 := by decide +kernel
      rw [hwV] at hw
      rw [hP.v_weight_eight_seven_one hHP.1 hHP.2 hV hw]
      simp [eventCount,hV]
  have htotal : (∑ H ∈ (hP.kfaces_finite 4).toFinset, tcnt P H (7,11,6)) = 2 := by
    rw [Finset.sum_congr rfl heq]
    exact hs
  have hdvd := hP.four_dvd_sum_tcnt (7,11,6)
  rw [htotal] at hdvd
  omega


namespace TwoPairPositiveProfile

def g4s2PairsA : List Row :=
  [excRow,excRow,excRow,excRow,excRow,⟨7,17,18,8,36⟩,
   ⟨7,17,18,8,36⟩,⟨8,18,17,7,35⟩,⟨8,18,17,7,36⟩]

def g4s2PairsC : List Row :=
  [excRow,excRow,excRow,excRow,excRow,excRow,
   ⟨7,17,18,8,36⟩,⟨8,18,17,7,36⟩,⟨8,20,21,9,42⟩]

def g4s2PairsD : List Row :=
  [excRow,excRow,excRow,excRow,excRow,excRow,
   ⟨7,17,18,8,36⟩,⟨8,19,19,8,39⟩,⟨8,19,19,8,39⟩]

omit hP in
/-- A small explicit multiplicity certificate avoids recomputing the search. -/
lemma profile_mem_of_count_certificate (G S : ℤ) (l : List Row)
    (hc : expandRows catalogue (fun R => l.count R) = l ∧
      l.length = 9 ∧ (l.map fullIndicator).sum = 2 ∧
      (l.map ridgeExcess).sum ≤ 4 ∧ admissible G S l) : l ∈ profiles G S := by
  obtain ⟨he,hn,hf,hb,ha⟩ := hc
  have hm := searchRows_complete catalogue (fun R => l.count R) 9 2 4
    (by rw [he]; exact hn) (by rw [he]; exact hf) (by rw [he]; exact hb)
  rw [he] at hm
  unfold profiles
  exact List.mem_filter.2 ⟨hm,decide_eq_true ha⟩

omit hP in
lemma g4s2_all_member : ∀ l ∈ [g4s2PairsA,g4s2ExcludedPairs,g4s2PairsC,g4s2PairsD],
    l ∈ profiles 4 2 := by
  intro l hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
    exact profile_mem_of_count_certificate 4 2 _ (by decide +kernel)

omit hP in
lemma g4s2_length : (profiles 4 2).length = 4 := by
  have h := profile_counts
  simp only [TwoPairPositive.remainingCells_eq,List.map_cons,List.map_nil,
    List.cons.injEq,and_true] at h
  exact h.2.2.2.2.2.1

omit hP in
lemma g4s2_perm : (profiles 4 2).Perm
    [g4s2PairsA,g4s2ExcludedPairs,g4s2PairsC,g4s2PairsD] := by
  have hn : [g4s2PairsA,g4s2ExcludedPairs,g4s2PairsC,g4s2PairsD].Nodup := by decide +kernel
  exact ((hn.subperm g4s2_all_member).perm_of_length_le (by rw [g4s2_length]; rfl)).symm

end TwoPairPositiveProfile

/-- This profile is excluded irrespective of the stress cell named in the assumptions. -/
theorem IsCSPolytope5.fewFull18_positive_g4s2_profile_ne
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) : positivePairRows P ≠ g4s2ExcludedPairs := by
  intro heq
  have he := (hP.fewFull18_positive_pair_budgets hv hh h1 h6 hlt).2.2.2.2.1
  rw [heq] at he
  have hsum : (g4s2ExcludedPairs.map Row.e).sum = 145 := by decide +kernel
  rw [hsum] at he
  have hS : (flagDataOf P).Gs = 2 := by omega
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [heq] at hp
  exact hP.two_pair_g4s2_excluded_profile_false hv hh h1 h6 hlt hS hp

/-- Three explicit candidates remain in the (4,2) cell. -/
theorem IsCSPolytope5.fewFull18_positive_g4s2_three_profiles
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243)
    (hG : (flagDataOf P).G = 4) (hS : (flagDataOf P).Gs = 2) :
    positivePairRows P ∈ [TwoPairPositiveProfile.g4s2PairsA,
      TwoPairPositiveProfile.g4s2PairsC,TwoPairPositiveProfile.g4s2PairsD] := by
  have hm := hP.fewFull18_positive_cell_profile_mem hv hh h1 h6 hlt
  rw [hG,hS] at hm
  have hm' := TwoPairPositiveProfile.g4s2_perm.mem_iff.1 hm
  have hn := hP.fewFull18_positive_g4s2_profile_ne hv hh h1 h6 hlt
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm' ⊢
  tauto

end Kalai5
