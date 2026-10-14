import Kalai5.Endpoints.TwoPairPositivePrismProfile

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A V facet of weight at most ten has exactly one of the two positive
vertex-minus-face ridge types. -/
theorem IsCSPolytope5.v_weight_ten_event_one
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,19,19,8,39⟩)
    (hW : q55w P F + 2 * exc P F ≤ 10) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = 1 := by
  have hR' := hR
  simp only [faceRow,Row.mk.injEq] at hR'
  obtain ⟨hn,_,hp,hr,hJ⟩ := hR'
  obtain ⟨c1,c2,c3,c4⟩ := hP.facet8_arith hF h4 hn
  simp only [hr,hJ,hp] at c1 c2 c3
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hw := hP.q55w_eq_b55 F
  have hq := hP.q4_add_big_le_exc F
  by_cases hb : (b55set P F).ncard = 0
  · have hq2 : q4 P F ≤ 2 := by omega
    have hpr : tcnt P F (6,9,5) = 0 := by
      by_contra hn
      have ht := hP.b55_add_three_le_of_prism (by omega : 1 ≤ tcnt P F (6,9,5))
      omega
    have h7lo : 1 ≤ tcnt P F (7,11,6) := by omega
    have hs := (hP.facet8_local hF h4).2.1 h7lo
    omega
  · have h7 (e p : ℕ) : tcnt P F (7,e,p) = 0 := by
      by_contra hz
      obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,e,p))
      have ht7 : cnt P T 0 = 7 := congrArg Prod.fst ht
      exact hb (hP.facet_T7 hF h4 hn hT hTF hT3 ht7).1
    have h7a := h7 11 6
    have h7b := h7 12 7
    have h7c := h7 13 8
    have h7d := h7 14 9
    have h7e := h7 15 10
    have hprlo : 1 ≤ tcnt P F (6,9,5) := by omega
    have hprhi : tcnt P F (6,9,5) ≤ 1 := by
      by_contra hn
      have ht := hP.b55_add_five_le_of_two_prisms (by omega : 2 ≤ tcnt P F (6,9,5))
      omega
    omega


theorem IsCSPolytope5.c_weight_five_event_zero
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨8,20,20,8,39⟩)
    (hW : q55w P F + 2 * exc P F ≤ 5) :
    tcnt P F (6,9,5) + tcnt P F (7,11,6) = 0 := by
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hn : cnt P F 0 = 8 := congrArg Row.n hR
  have h7 := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega) 11 6
  have hp : tcnt P F (6,9,5) = 0 := by
    by_contra hz
    have hw := hP.c20_prism_weight_nine hF h4 hR (by omega)
    omega
  omega

theorem IsCSPolytope5.small_facet_seven_ridge_zero
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) (e p : ℕ) : tcnt P F (7,e,p) = 0 := by
  by_contra hz
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (7,e,p))
  have hT7 : cnt P T 0 = 7 := congrArg Prod.fst ht
  have hne : T ≠ F := by intro he; subst T; omega
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  omega

theorem IsCSPolytope5.r0_prism_zero
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨7,17,18,8,36⟩) : tcnt P F (6,9,5) = 0 := by
  have hn : cnt P F 0 = 7 := congrArg Row.n hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 = (⟨7,17,18,8,36⟩ : Row) →
      X.2.1 = [4,4,0,0,0,0,0] := by decide +kernel
  have hp := hcheck _ hm (by change rowOf F = _; rw [he,hR])
  obtain ⟨_,_,_,hc,_,_,_⟩ := hP.profile_counts hF h4 hn.le hp
  rw [hP.tcnt_eq_card]
  exact hc

/-- A global slack bound bounds each individual facet's nonnegative deficit. -/
theorem IsCSPolytope5.facet_weight_le_of_row_sum
    (B L : ℤ)
    (hbudget : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55w P H + 2 * exc P H)) ≤ B)
    (hsum : (((facetRows P).map q55BSixRowWeight).sum : ℤ) = L)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (q55BSixRowWeight (faceRow P F) : ℤ) + (B-L) := by
  rw [hP.facetRows_sum q55BSixRowWeight,Nat.cast_sum] at hsum
  have hnonneg : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      0 ≤ q55w P H + 2 * exc P H - (q55BSixRowWeight (faceRow P H) : ℤ) := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    have hl := hP.q55_bSix_row_weight hH.1 hH.2
    omega
  have hm : F ∈ (hP.kfaces_finite 4).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩
  have ht := Finset.single_le_sum hnonneg hm
  rw [Finset.sum_sub_distrib] at ht
  omega


omit hP in
def g4s4Pairs : List Row :=
  [excRow,excRow,excRow,excRow,excRow,excRow,
   ⟨7,17,18,8,36⟩,⟨8,19,19,8,39⟩,⟨8,20,20,8,39⟩]

theorem IsCSPolytope5.two_pair_g4s4_weight_upper
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 4)
    (hprof : (facetRows P).Perm (g4s4Pairs ++ g4s4Pairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (q55BSixRowWeight (faceRow P F) : ℤ) + 2 := by
  have hsum : (((facetRows P).map q55BSixRowWeight).sum : ℤ) = 130 := by
    rw [(hprof.map q55BSixRowWeight).sum_eq]
    decide +kernel
  have hu := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hu
  norm_num at hu
  simpa using hP.facet_weight_le_of_row_sum 132 130 hu hsum hF h4

theorem IsCSPolytope5.two_pair_g4s4_profile_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 4)
    (hprof : (facetRows P).Perm (g4s4Pairs ++ g4s4Pairs)) : False := by
  let eventCount : Row → ℕ := fun R =>
    if R = excRow ∨ R = ⟨8,19,19,8,39⟩ then 1 else 0
  have hs : ((facetRows P).map eventCount).sum = 14 := by
    rw [(hprof.map eventCount).sum_eq]
    decide +kernel
  rw [hP.facetRows_sum eventCount] at hs
  have heq : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      tcnt P H (6,9,5) + tcnt P H (7,11,6) = eventCount (faceRow P H) := by
    intro H hH
    have hHP := hH
    rw [Set.Finite.mem_toFinset] at hHP
    have hm : faceRow P H ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨H,Finset.mem_toList.2 hH,rfl⟩
    have hm' := hprof.mem_iff.1 hm
    have hcases : faceRow P H = excRow ∨ faceRow P H = ⟨7,17,18,8,36⟩ ∨
        faceRow P H = ⟨8,19,19,8,39⟩ ∨ faceRow P H = ⟨8,20,20,8,39⟩ := by
      simpa only [g4s4Pairs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
        or_self,or_self_left,or_assoc] using hm'
    have hw := hP.two_pair_g4s4_weight_upper hv hh h1 h6 hlt hS hprof hHP.1 hHP.2
    rcases hcases with hY | hR0 | hV | hC
    · have hn : cnt P H 0 = 7 := congrArg Row.n hY
      rw [hP.Y_prism_count hHP.1 hHP.2 hY,
        hP.small_facet_seven_ridge_zero hHP.1 hHP.2 hn.le 11 6]
      simp [eventCount,hY]
    · have hn : cnt P H 0 = 7 := congrArg Row.n hR0
      rw [hP.r0_prism_zero hHP.1 hHP.2 hR0,
        hP.small_facet_seven_ridge_zero hHP.1 hHP.2 hn.le 11 6]
      simp [eventCount,hR0,excRow]
    · rw [hV] at hw
      have hwV : q55BSixRowWeight (⟨8,19,19,8,39⟩ : Row) = 8 := by decide +kernel
      rw [hwV] at hw
      rw [hP.v_weight_ten_event_one hHP.1 hHP.2 hV (by omega)]
      simp [eventCount,hV]
    · rw [hC] at hw
      have hwC : q55BSixRowWeight (⟨8,20,20,8,39⟩ : Row) = 3 := by decide +kernel
      rw [hwC] at hw
      rw [hP.c_weight_five_event_zero hHP.1 hHP.2 hC (by omega)]
      simp [eventCount,hC,excRow]
  have htotal : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (tcnt P H (6,9,5) + tcnt P H (7,11,6))) = 14 := by
    rw [Finset.sum_congr rfl heq]
    exact hs
  have hdvd : 4 ∣ (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (tcnt P H (6,9,5) + tcnt P H (7,11,6))) := by
    rw [Finset.sum_add_distrib]
    exact dvd_add (hP.four_dvd_sum_tcnt (6,9,5)) (hP.four_dvd_sum_tcnt (7,11,6))
  rw [htotal] at hdvd
  omega

end Kalai5
