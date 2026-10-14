import Kalai5.Endpoints.E18positive.G2S2
import Kalai5.Endpoints.E18positive.G2S4
import Kalai5.Endpoints.E18positive.G2S6
import Kalai5.Endpoints.E18positive.G2S8
import Kalai5.Endpoints.E18positive.G2S10
import Kalai5.Endpoints.E18positive.G4S2
import Kalai5.Endpoints.E18positive.G4S4
import Kalai5.Endpoints.E18positive.G4S6
import Kalai5.Endpoints.TwoPairPositiveRows

/-! Complete parity coverage of the remaining cells fixes the global counts. -/
namespace Kalai5.E18positive

theorem globals
    (C : Ctx 16 18 8 9 (tRow :: fake8) (u9Row :: qRow :: tRow :: fake8))
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hcell : (C.D.G, C.D.Gs) ∈ TwoPairPositive.remainingCells)
    (hcap : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2)
    (hcnt : cntBig C.F.rows (C.D.G - 2) ≤ 2)
    (hc8 : cnt8 C.F.rows = 4) (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55BFiveRowWeight).sum : ℤ) ≤
      4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) (hI : C.D.I ≤ 130)
    (hI2 : C.D.G = 2 → C.D.I = 130) :
    C.D.e = 58 ∧ C.D.r = 60 ∧ C.D.I = 130 := by
  rw [TwoPairPositive.remainingCells_eq] at hcell
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hcell
  rcases hcell with h | h | h | h | h | h | h | h
  · exact globals_g2s2 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g2s4 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g2s6 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g2s8 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g2s10 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g4s2 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g4s4 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2
  · exact globals_g4s6 C hJF hJS h.1 h.2 hcap (by simpa [h.1] using hcnt) hc8 hs8 hql ht hI hI2

end Kalai5.E18positive

namespace Kalai5
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

noncomputable def IsCSPolytope5.ctx16positive
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hT : tRow ∉ facetRows P) (hQ : qRow ∉ facetRows (polarSet P))
    (hTs : tRow ∉ facetRows (polarSet P)) :
    Ctx 16 18 8 9 (tRow :: fake8) (u9Row :: qRow :: tRow :: fake8) :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh,
    hP.rowOK_P_le (nmax := 8) (fun R hR => by have := hP.facetRows_n_le R hR; omega)
      (fun R hR hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hT hR
        · exact hP.facetRows_not_fake8 R hR hx),
    hP.rowOK_S (by omega) (fun R hR hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hP.u9Row_not_mem_polar_16_18 hv hh hR
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hQ hR
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hTs hR
      · exact hP.polar.facetRows_not_fake8 R hR hx),
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

/-- Every remaining counterexample has the same edge, ridge and vertex-facet counts. -/
theorem IsCSPolytope5.fewFull18_positive_globals
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (flagDataOf P).e = 58 ∧ (flagDataOf P).r = 60 ∧ (flagDataOf P).I = 130 := by
  obtain ⟨hc, hcell, _, hi, hg, hi2⟩ := hP.fewFull18_positive_constraints hv hh h1 h6 hlt
  obtain ⟨_, hQ, hTs⟩ := hP.fewFull18_polar_products_excluded hv hh h1 h6 hlt
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  let C := hP.ctx16positive hv hh hT hQ hTs
  have hcap : ∀ R ∈ facetRows P, 2 * R.g ≤ 2 := fun R hR => by have := hg R hR; omega
  have hcnt : cntBig (facetRows P) ((flagDataOf P).G - 2) ≤ 2 := by
    by_cases hj : ∃ R ∈ facetRows P, 1 ≤ R.g
    · simpa only [Int.reduceMul] using hP.cntBig_le_two' hj
    · have hG0 := hP.flagData_valid.G_nonneg
      apply cntBig_le_of_cap
      intro R hR
      have hn : ¬ 1 ≤ R.g := fun h => hj ⟨R, hR, h⟩
      have hG : (flagDataOf P).G = 2 ∨ (flagDataOf P).G = 4 := by
        rw [TwoPairPositive.remainingCells_eq] at hcell
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hcell
        omega
      omega
  have hs := hP.full_ridge_rows hv
  rw [hh, hc] at hs
  exact E18positive.globals C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
    hcell hcap hcnt hc (by change sumR8 (facetRows P) ≤ 36; omega)
    (hP.q55_bFive_rows hv) (hP.t_le_of_faces_lt hlt)
    hi (fun hG => (hi2 hG).1)

/-- Saturated incidence forces every remaining facet to have seven or eight vertices. -/
theorem IsCSPolytope5.fewFull18_positive_rows_ge_seven
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) : ∀ R ∈ facetRows P, 7 ≤ R.n := by
  have hc := (hP.fewFull18_residual_two_positive hv hh h1 h6 hlt).1
  have hi := (hP.fewFull18_positive_globals hv hh h1 h6 hlt).2.2
  apply seven_le_n_of_incidence_saturated
  · intro R hR
    have := hP.facetRows_n_le R hR
    omega
  · rw [hP.facetRows_sum_n, hP.facetRows_length, hh, hc]
    exact hi

/-- The sole remaining face vector is (16,58,86,60,18), with 239 nonempty faces. -/
theorem IsCSPolytope5.fewFull18_positive_face_numbers
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    fvec P 1 = 58 ∧ fvec P 2 = 86 ∧ fvec P 3 = 60 ∧
    (flagDataOf P).I = 130 ∧ (faces P).ncard = 239 := by
  obtain ⟨he, hr, hi⟩ := hP.fewFull18_positive_globals hv hh h1 h6 hlt
  have hEuler := hP.flagData_valid.euler
  have hvD : (flagDataOf P).v = 16 := hv
  have hhD : (flagDataOf P).h = 18 := hh
  rw [hvD, hhD, he, hr] at hEuler
  have hp : (flagDataOf P).p = 86 := by omega
  refine ⟨he, hp, hr, hi, ?_⟩
  have ht := FlagData.total_eq hP.flagData_valid
  have hf := hP.faces_ncard
  change (faces P).ncard = (flagDataOf P).total at hf
  norm_num [FlagData.t, he, hr] at ht
  omega

/-- Positive-stress rows form one antipodal pair at G=2 and three at G=4. -/
theorem IsCSPolytope5.fewFull18_positive_stress_count
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (cntBig (facetRows P) 0 : ℤ) = 2 * (flagDataOf P).G - 2 := by
  obtain ⟨_, _, _, _, hg, _⟩ := hP.fewFull18_positive_constraints hv hh h1 h6 hlt
  have heq := sum_g_eq_cntBig_zero (facetRows P) hP.facet_g_nonneg hg
  have hs := hP.facet_stress_sum_16_18 hv hh
  have hi := (hP.fewFull18_positive_globals hv hh h1 h6 hlt).2.2
  rw [hi] at hs
  omega

/-- The residual row-weight budget depends only on polar stress. -/
theorem IsCSPolytope5.fewFull18_positive_weight_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((facetRows P).map q55BFiveRowWeight).sum : ℤ) ≤ 156 - 6 * (flagDataOf P).Gs := by
  obtain ⟨he, hp, hr, hi, _⟩ := hP.fewFull18_positive_face_numbers hv hh h1 h6 hlt
  change (flagDataOf P).e = 58 at he
  change (flagDataOf P).p = 86 at hp
  change (flagDataOf P).r = 60 at hr
  have hhD : (flagDataOf P).h = 18 := hh
  have hw := hP.q55_bFive_rows hv
  have hf := hP.flagData_valid.f024_eq
  simp only [FlagData.A, FlagData.Gs, he, hp, hr, hi, hhD] at hw hf ⊢
  push_cast at hw hf ⊢
  linarith

/-- The strengthened B19 weight has the same global budget. -/
theorem IsCSPolytope5.fewFull18_positive_bSix_weight_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (((facetRows P).map q55BSixRowWeight).sum : ℤ) ≤ 156 - 6 * (flagDataOf P).Gs := by
  obtain ⟨he, hp, hr, hi, _⟩ := hP.fewFull18_positive_face_numbers hv hh h1 h6 hlt
  change (flagDataOf P).e = 58 at he
  change (flagDataOf P).p = 86 at hp
  change (flagDataOf P).r = 60 at hr
  have hhD : (flagDataOf P).h = 18 := hh
  have hw := hP.q55_bSix_rows hv
  have hf := hP.flagData_valid.f024_eq
  simp only [FlagData.A, FlagData.Gs, he, hp, hr, hi, hhD] at hw hf ⊢
  push_cast at hw hf ⊢
  linarith

end Kalai5
