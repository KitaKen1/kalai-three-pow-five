import Kalai5.Endpoints.TwoPairZeroClosure
import Kalai5.Endpoints.NoU

/-! Local stress and incidence restrictions for the remaining two-pair cells. -/
namespace Kalai5
open scoped Classical

/-- Positive local stresses are bounded by their number times a uniform cap. -/
lemma sum_g_le_mul_cntBig_zero (rows : List Row) (b : ℤ)
    (h0 : ∀ R ∈ rows, 0 ≤ R.g) (hb : ∀ R ∈ rows, R.g ≤ b) :
    (rows.map Row.g).sum ≤ b * cntBig rows 0 := by
  induction rows with
  | nil => simp [cntBig]
  | cons R rs ih =>
    have hr0 := h0 R (List.mem_cons_self ..)
    have hrb := hb R (List.mem_cons_self ..)
    have ht := ih (fun S hS => h0 S (List.mem_cons_of_mem R hS))
      (fun S hS => hb S (List.mem_cons_of_mem R hS))
    by_cases h : 0 < 2 * R.g
    · have hpos : 0 < R.g := by omega
      simp [cntBig,hpos] at ht ⊢
      push_cast
      nlinarith
    · have hz : R.g = 0 := by omega
      simpa [cntBig,h,hz] using ht

/-- For integral stresses zero or one, the stress sum counts positive rows. -/
lemma sum_g_eq_cntBig_zero (rows : List Row)
    (h0 : ∀ R ∈ rows, 0 ≤ R.g) (h1 : ∀ R ∈ rows, R.g ≤ 1) :
    (rows.map Row.g).sum = (cntBig rows 0 : ℤ) := by
  induction rows with
  | nil => simp [cntBig]
  | cons R rs ih =>
    have hr0 := h0 R (List.mem_cons_self ..)
    have hr1 := h1 R (List.mem_cons_self ..)
    have ht := ih (fun S hS => h0 S (List.mem_cons_of_mem R hS))
      (fun S hS => h1 S (List.mem_cons_of_mem R hS))
    by_cases h : 0 < 2 * R.g
    · have hg : R.g = 1 := by omega
      simpa [cntBig, h, hg, Nat.cast_add, add_comm] using congrArg (fun x : ℤ => 1 + x) ht
    · have hg : R.g = 0 := by omega
      simpa [cntBig, h, hg] using ht

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.two_pair_incidence_le_130
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4) :
    (flagDataOf P).I ≤ 130 := by
  have hn : ∀ R ∈ facetRows P, R.n ≤ 8 := fun R hR => by
    have := hP.facetRows_n_le R hR
    omega
  have hi := sum_n_le_seven_length_add_cnt8 (facetRows P) hn
  rw [hP.facetRows_sum_n,hP.facetRows_length,hh,hc] at hi
  exact hi

lemma IsCSPolytope5.facet_stress_sum_16_18
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) :
    ((facetRows P).map Row.g).sum = 2 * (flagDataOf P).G + 128 - (flagDataOf P).I := by
  have hs := hP.rowsData.sum_g hP.flagData_valid
  change ((facetRows P).map Row.g).sum = _ at hs
  have hvD : (flagDataOf P).v = 16 := hv
  have hhD : (flagDataOf P).h = 18 := hh
  rw [hvD,hhD] at hs
  norm_num at hs
  linarith

/-- At G=2 the unique positive-stress pair saturates the vertex incidence bound. -/
theorem IsCSPolytope5.two_pair_G2_incidence
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 2) :
    (flagDataOf P).I = 130 ∧ cntBig (facetRows P) 0 = 2 := by
  have hi := hP.two_pair_incidence_le_130 hv hh hc
  have hs := hP.facet_stress_sum_16_18 hv hh
  rw [hG] at hs
  have hrow := hP.rowOK_P_le (nmax := 8)
    (fun R hR => by have := hP.facetRows_n_le R hR; omega)
    (show ∀ R ∈ facetRows P, R ∉ ([] : List Row) from fun _ _ => List.not_mem_nil)
  have hcap : ∀ R ∈ facetRows P, R.g ≤ 1 := by
    intro R hR
    have := (hrow R hR).g_le
    rw [hG] at this
    omega
  have hcount : cntBig (facetRows P) 0 ≤ 2 := by
    rcases rows_split_max (facetRows P) 1 with hx | hx
    · have ht := hP.cntBig_le_two' hx
      simpa only [hG,Int.reduceMul,Int.reduceSub] using ht
    · exact cntBig_le_of_cap (by simpa using hx)
  have hl := sum_g_le_mul_cntBig_zero (facetRows P) 1
    (fun R hR => (hrow R hR).g_nonneg) hcap
  simp only [one_mul] at hl
  constructor <;> omega

/-- Every facet in the G=2 two-pair case has seven or eight vertices. -/
theorem IsCSPolytope5.two_pair_G2_rows_ge_seven
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 2) : ∀ R ∈ facetRows P, 7 ≤ R.n := by
  apply seven_le_n_of_incidence_saturated
  · intro R hR
    have := hP.facetRows_n_le R hR
    omega
  · rw [hP.facetRows_sum_n,hP.facetRows_length,hh,hc]
    exact (hP.two_pair_G2_incidence hv hh hc hG).1

/-- G=4 still permits no local stress two: one such pair would leave too little total stress. -/
theorem IsCSPolytope5.two_pair_G4_local_stress_le_one
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 4) : ∀ R ∈ facetRows P, R.g ≤ 1 := by
  have hi := hP.two_pair_incidence_le_130 hv hh hc
  have hs := hP.facet_stress_sum_16_18 hv hh
  rw [hG] at hs
  have hrow := hP.rowOK_P_le (nmax := 8)
    (fun R hR => by have := hP.facetRows_n_le R hR; omega)
    (show ∀ R ∈ facetRows P, R ∉ ([] : List Row) from fun _ _ => List.not_mem_nil)
  have hcap : ∀ R ∈ facetRows P, R.g ≤ 2 := by
    intro R hR
    have := (hrow R hR).g_le
    rw [hG] at this
    omega
  intro R hR
  by_contra hbad
  have ht := hP.cntBig_le_two' (j := 2) ⟨R,hR,by omega⟩
  have hcount : cntBig (facetRows P) 0 ≤ 2 := by
    simpa only [hG,Int.reduceMul,Int.reduceSub] using ht
  have hl := sum_g_le_mul_cntBig_zero (facetRows P) 2
    (fun R hR => (hrow R hR).g_nonneg) hcap
  omega

/-- All remaining cells have only local stress zero or one. -/
theorem IsCSPolytope5.two_pair_positive_local_stress_le_one
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hG : (flagDataOf P).G = 2 ∨ (flagDataOf P).G = 4) :
    ∀ R ∈ facetRows P, R.g ≤ 1 := by
  rcases hG with hG | hG
  · intro R hR
    have hrow := hP.rowOK_P_le (nmax := 8)
      (fun S hS => by have := hP.facetRows_n_le S hS; omega)
      (show ∀ S ∈ facetRows P, S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil)
    have := (hrow R hR).g_le
    rw [hG] at this
    omega
  · exact hP.two_pair_G4_local_stress_le_one hv hh hc hG

/-- Geometric constraints to retain when passing the eight cells to a finite search. -/
theorem IsCSPolytope5.fewFull18_positive_constraints
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    cnt8 (facetRows P) = 4 ∧
    ((flagDataOf P).G, (flagDataOf P).Gs) ∈ TwoPairPositive.remainingCells ∧
    u9Row ∉ facetRows (polarSet P) ∧
    (flagDataOf P).I ≤ 130 ∧
    (∀ R ∈ facetRows P, R.g ≤ 1) ∧
    ((flagDataOf P).G = 2 →
      (flagDataOf P).I = 130 ∧ cntBig (facetRows P) 0 = 2 ∧
      ∀ R ∈ facetRows P, 7 ≤ R.n) := by
  obtain ⟨hc, hcell⟩ := hP.fewFull18_residual_two_positive hv hh h1 h6 hlt
  have hG : (flagDataOf P).G = 2 ∨ (flagDataOf P).G = 4 := by
    have ht := hcell
    rw [TwoPairPositive.remainingCells_eq] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    omega
  refine ⟨hc, hcell, hP.u9Row_not_mem_polar_16_18 hv hh,
    hP.two_pair_incidence_le_130 hv hh hc,
    hP.two_pair_positive_local_stress_le_one hv hh hc hG, ?_⟩
  intro hG2
  obtain ⟨hi, hn⟩ := hP.two_pair_G2_incidence hv hh hc hG2
  exact ⟨hi, hn, hP.two_pair_G2_rows_ge_seven hv hh hc hG2⟩

/-- At excess three, weight five would require exactly two quadrilaterals, which is impossible. -/
lemma IsCSPolytope5.q55_weight_ne_five_of_exc_three (F : Set E5)
    (he : exc P F = 3) : q55w P F + 2 * exc P F ≠ 5 := by
  have hb := hP.q4_add_big_le_exc F
  have hw := hP.q55w_eq_b55 F
  intro hfive
  have hq2 : q4 P F = 2 := by omega
  have hbig : big2 P F = 0 := by omega
  have hq := hP.exc_eq_q4_of_big F hbig
  omega

/-- The B19 weight improves from five to six by its discrete spectrum, not by evenness. -/
theorem IsCSPolytope5.q55_b_six {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = ⟨8,19,19,8,38⟩) :
    6 ≤ q55w P F + 2 * exc P F := by
  have hfive := hP.q55_b_five hF h4 hR
  have he := hP.exc_eq_faceRow hF h4
  rw [hR] at he
  norm_num at he
  have hne := hP.q55_weight_ne_five_of_exc_three F he
  omega

omit hP in
def q55BSixRowWeight (R : Row) : ℕ :=
  if R = ⟨8,19,19,8,38⟩ then 6 else q55BFiveRowWeight R

omit hP in
lemma q55BFiveRowWeight_le_bSix (R : Row) : q55BFiveRowWeight R ≤ q55BSixRowWeight R := by
  unfold q55BSixRowWeight
  split_ifs with h
  · subst R; decide +kernel
  · exact le_rfl

theorem IsCSPolytope5.q55_bSix_row_weight {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) :
    (q55BSixRowWeight (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F := by
  unfold q55BSixRowWeight
  split_ifs with h
  · exact hP.q55_b_six hF h4 h
  · exact hP.q55_bFive_row_weight hF h4

theorem IsCSPolytope5.q55_bSix_rows (hv : fvec P 0 = 16) :
    (((facetRows P).map q55BSixRowWeight).sum : ℤ) ≤
      4 * (flagDataOf P).A + 2 * ((flagDataOf P).f024 - 3 * ((flagDataOf P).y : ℤ)) := by
  rw [hP.facetRows_sum q55BSixRowWeight, Nat.cast_sum]
  exact (Finset.sum_le_sum (fun F hF => by
    rw [Set.Finite.mem_toFinset] at hF
    exact hP.q55_bSix_row_weight hF.1 hF.2)).trans (hP.q55 hv)

end Kalai5
