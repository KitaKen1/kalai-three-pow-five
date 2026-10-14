import Kalai5.Endpoints.E18q.Cells
import Kalai5.Endpoints.SixteenWeighted

/-!
# Geometric consequences of the strong Q55 certificates at (16,18)

The high-polar-stress range and four explicitly listed cells are completely
proved. These results do not assert coverage of all of `FewFull16 18`.
-/

namespace Kalai5

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Counterexamples have even `e+r` at most 118. -/
lemma IsCSPolytope5.t_le_of_faces_lt (hlt : (faces P).ncard < 243) :
    ((flagDataOf P).t : ℤ) ≤ 118 := by
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    exact hlt
  have : (flagDataOf P).t ≤ 118 := by
    by_contra h
    exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
  exact_mod_cast this

/-- At (16,18), one to three full-facet pairs and polar stress at least sixteen
already imply the face bound, with no exclusions on the polar's actual rows. -/
theorem IsCSPolytope5.three_pow_five_16_18_Gs_ge_sixteen
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hS : 16 ≤ (flagDataOf P).Gs) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  have hD := hP.flagData_valid
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hs : sumR8 (facetRows P) ≤ 16 := by rw [hk] at hridge; omega
    exact E18q.leaf_k1_s16 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hD.G_nonneg hS (by show cnt8 (facetRows P) = 2; omega) hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 36 := by rw [hk] at hridge; omega
    exact E18q.leaf_k2_s16 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hD.G_nonneg hS (by show cnt8 (facetRows P) = 4; omega) hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 60 := by rw [hk] at hridge; omega
    exact E18q.leaf_k3_s16 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hD.G_nonneg hS (by show cnt8 (facetRows P) = 6; omega) hs (hP.q55_strong_rows hv) ht

/-- Four additional cells, closed by exact row costs and exhaustive even/stress
branching. The count is the physical number of full facets, twice kP. -/
theorem IsCSPolytope5.three_pow_five_16_18_strong_cells
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hcell :
      (cnt8 (facetRows P) = 4 ∧ (flagDataOf P).G = 2 ∧ (flagDataOf P).Gs = 12) ∨
      (cnt8 (facetRows P) = 4 ∧ (flagDataOf P).G = 4 ∧ (flagDataOf P).Gs = 8) ∨
      (cnt8 (facetRows P) = 6 ∧ (flagDataOf P).G = 6 ∧ (flagDataOf P).Gs = 12) ∨
      (cnt8 (facetRows P) = 6 ∧ (flagDataOf P).G = 8 ∧ (flagDataOf P).Gs = 4)) :
    243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) →
      cntBig C.F.rows (C.D.G - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two' hj
  have hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) →
      cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two_polar hj
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  rcases hcell with ⟨hc, hG, hS⟩ | ⟨hc, hG, hS⟩ | ⟨hc, hG, hS⟩ | ⟨hc, hG, hS⟩
  · have hs : sumR8 (facetRows P) ≤ 36 := by rw [hc] at hridge; omega
    exact E18q.cell_k2_g2s12 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG hS hc hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 36 := by rw [hc] at hridge; omega
    exact E18q.cell_k2_g4s8 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG hS hc hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 60 := by rw [hc] at hridge; omega
    exact E18q.cell_k3_g6s12 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG hS hc hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 60 := by rw [hc] at hridge; omega
    exact E18q.cell_k3_g8s4 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG hS hc hs (hP.q55_strong_rows hv) ht

/-- High primal stress closes at sixteen for one or two full pairs, and at
eighteen for three full pairs. -/
theorem IsCSPolytope5.three_pow_five_16_18_high_G
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hG : (cnt8 (facetRows P) ≤ 4 ∧ 16 ≤ (flagDataOf P).G) ∨
      18 ≤ (flagDataOf P).G) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  have hD := hP.flagData_valid
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hs : sumR8 (facetRows P) ≤ 16 := by rw [hk] at hridge; omega
    exact E18q.leaf_k1_g16 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      (by change 16 ≤ (flagDataOf P).G; omega) hD.Gs_nonneg
      (by show cnt8 (facetRows P) = 2; omega) hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 36 := by rw [hk] at hridge; omega
    exact E18q.leaf_k2_g16 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      (by change 16 ≤ (flagDataOf P).G; omega) hD.Gs_nonneg
      (by show cnt8 (facetRows P) = 4; omega) hs (hP.q55_strong_rows hv) ht
  · have hs : sumR8 (facetRows P) ≤ 60 := by rw [hk] at hridge; omega
    exact E18q.leaf_k3_g18 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      (by change 18 ≤ (flagDataOf P).G; omega) hD.Gs_nonneg
      (by show cnt8 (facetRows P) = 6; omega) hs (hP.q55_strong_rows hv) ht

/-- The boundary G = 16 with three full pairs is covered for every even Gs ≤ 14. -/
theorem IsCSPolytope5.three_pow_five_16_18_G_eq_sixteen
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 6) (hG : (flagDataOf P).G = 16)
    (hS : (flagDataOf P).Gs ≤ 14) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  have hD := hP.flagData_valid
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) →
      cntBig C.F.rows (C.D.G - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two' hj
  have hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) →
      cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two_polar hj
  have hridge := hP.full_ridge_rows hv
  rw [hh, hc] at hridge
  have hs8 : sumR8 (facetRows P) ≤ 60 := by omega
  obtain ⟨s, hs⟩ := C.even_Gs
  change (flagDataOf P).Gs = s + s at hs
  have hs0 : 0 ≤ s := by have := hD.Gs_nonneg; omega
  have hs7 : s ≤ 7 := by omega
  interval_cases s
  · exact E18q.cell_k3_g16s0 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 0; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s2 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 2; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s4 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 4; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s6 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 6; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s8 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 8; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s10 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 10; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s12 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 12; omega) hc hs8
      (hP.q55_strong_rows hv) ht
  · exact E18q.cell_k3_g16s14 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hG (by change (flagDataOf P).Gs = 14; omega) hc hs8
      (hP.q55_strong_rows hv) ht

/-- All high-primal-stress cases close, including the boundary G = 16. -/
theorem IsCSPolytope5.three_pow_five_16_18_G_ge_sixteen
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hG : 16 ≤ (flagDataOf P).G) : 243 ≤ (faces P).ncard := by
  by_cases h18 : 18 ≤ (flagDataOf P).G
  · exact hP.three_pow_five_16_18_high_G hv hh h1 h6 (Or.inr h18)
  by_cases hc4 : cnt8 (facetRows P) ≤ 4
  · exact hP.three_pow_five_16_18_high_G hv hh h1 h6 (Or.inl ⟨hc4, hG⟩)
  by_cases hS : 16 ≤ (flagDataOf P).Gs
  · exact hP.three_pow_five_16_18_Gs_ge_sixteen hv hh h1 h6 hS
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  change (flagDataOf P).G = g + g at hg
  change (flagDataOf P).Gs = s + s at hs
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  obtain ⟨k, hk⟩ := hev
  exact hP.three_pow_five_16_18_G_eq_sixteen hv hh (by omega) (by omega) (by omega)

end Kalai5
