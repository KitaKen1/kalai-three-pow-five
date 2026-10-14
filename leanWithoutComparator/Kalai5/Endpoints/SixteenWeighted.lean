import Kalai5.Endpoints.E20w.Rectangles
import Kalai5.Endpoints.E20w.Closure
import Kalai5.Endpoints.SixteenFew

/-!
# Geometric context for the new few-full certificates

The prism row is handled by the full-prism theorem. The remaining exclusions
are precisely the six geometrically impossible rows in `fake8`.
-/

namespace Kalai5

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

noncomputable def IsCSPolytope5.ctx16w {h nS : ℕ} (hv : fvec P 0 = 16)
    (hh : fvec P 4 = h) (hS : h ≤ 2 * nS) (hT : tRow ∉ facetRows P) :
    Ctx 16 h 8 nS (tRow :: fake8) fake8 :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh,
    hP.rowOK_P_le (nmax := 8) (fun R hR => by have := hP.facetRows_n_le R hR; omega)
      (fun R hR hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hT hR
        · exact hP.facetRows_not_fake8 R hR hx),
    hP.rowOK_S (by omega) hP.polar.facetRows_not_fake8,
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

/-- The one-full-pair, zero-stress subcase of `(16,20)`, including the prism branch. -/
theorem IsCSPolytope5.three_pow_five_16_20_oneFull_G0
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 20)
    (hcnt : cnt8 (facetRows P) = 2) (hG : (flagDataOf P).G = 0) :
    243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    omega
  have ht : ((flagDataOf P).t : ℤ) ≤ 118 := by
    have : (flagDataOf P).t ≤ 118 := by
      by_contra h
      exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
    exact_mod_cast this
  have hridge := hP.full_ridge_rows hv
  rw [hh, hcnt] at hridge
  have hs8 : sumR8 (facetRows P) ≤ 18 := by omega
  let C := hP.ctx16w (nS := 10) hv hh (by norm_num) hT
  exact E20w.leaf_k1_g0 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
    hD.G_nonneg hG.le hD.Gs_nonneg (hP.A_eq_zero_of_G_eq_zero hG) hcnt hs8
    (hP.q55_rows hv) ht

/-- Sixteen vertices, twenty facets, and one to three antipodal full-facet pairs.
The Q55 weights, full-ridge bound, stress localization, and even flag counts
give an exhaustive certificate proof. -/
theorem IsCSPolytope5.three_pow_five_16_20_fewFull
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 20)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6) :
    243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    omega
  have ht : ((flagDataOf P).t : ℤ) ≤ 118 := by
    have : (flagDataOf P).t ≤ 118 := by
      by_contra h
      exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
    exact_mod_cast this
  let C := hP.ctx16w (nS := 10) hv hh (by norm_num) hT
  have hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) →
      cntBig C.F.rows (C.D.G - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two' hj
  have hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) →
      cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two_polar hj
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hs : sumR8 (facetRows P) ≤ 18 := by rw [hk] at hridge; omega
    exact E20w.closure1 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS (by show cnt8 (facetRows P) = 2; omega) hs (hP.q55_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 40 := by rw [hk] at hridge; omega
    exact E20w.closure2 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS (by show cnt8 (facetRows P) = 4; omega) hs (hP.q55_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 66 := by rw [hk] at hridge; omega
    exact E20w.closure3 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS (by show cnt8 (facetRows P) = 6; omega) hs (hP.q55_rows hv) ht

omit hP in
/-- The few-full-facet obligation at twenty facets. -/
theorem fewFull16_20 : FewFull16 20 := fun _ hP hv hh h1 h6 =>
  hP.three_pow_five_16_20_fewFull hv hh h1 h6

end Kalai5
