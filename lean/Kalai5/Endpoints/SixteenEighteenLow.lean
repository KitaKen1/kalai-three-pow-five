import Kalai5.Endpoints.E18low.Reduction
import Kalai5.Endpoints.SixteenEighteenWeighted
import Kalai5.FullProd.SideEdges
import Kalai5.FullProd.TF18g
import Kalai5.Rows.FullDeficit
import Kalai5.Rows.PolygonExcess

/-!
# Explicit residual cases at sixteen vertices and eighteen facets

The counterexample hypotheses reduce to 33 low-stress cells. A separate
certificate bounds the number of ridges by 62, excluding the two product rows
on the polar side through their geometric edge bounds.
-/

namespace Kalai5

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A counterexample must occur in the explicit list for its number of full pairs. -/
theorem IsCSPolytope5.fewFull18_residual
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (cnt8 (facetRows P) = 2 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18low.remainingCells 1) ∨
    (cnt8 (facetRows P) = 4 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18low.remainingCells 2) ∨
    (cnt8 (facetRows P) = 6 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18low.remainingCells 3) := by
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hGn : ¬ 16 ≤ (flagDataOf P).G := fun h =>
    (not_le_of_gt hlt) (hP.three_pow_five_16_18_G_ge_sixteen hv hh h1 h6 h)
  have hSn : ¬ 16 ≤ (flagDataOf P).Gs := fun h =>
    (not_le_of_gt hlt) (hP.three_pow_five_16_18_Gs_ge_sixteen hv hh h1 h6 h)
  have hG14 : C.D.G ≤ 14 := by
    obtain ⟨g, hg⟩ := FlagData.even_G C.hD
    change ¬ 16 ≤ C.D.G at hGn
    omega
  have hS14 : C.D.Gs ≤ 14 := by
    obtain ⟨s, hs⟩ := C.even_Gs
    change ¬ 16 ≤ C.D.Gs at hSn
    omega
  have ht := hP.t_le_of_faces_lt hlt
  have hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) →
      cntBig C.F.rows (C.D.G - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two' hj
  have hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) →
      cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2 := fun _ hj => hP.cntBig_le_two_polar hj
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hc : cnt8 (facetRows P) = 2 := by omega
    have hs : sumR8 (facetRows P) ≤ 16 := by rw [hc] at hridge; omega
    exact Or.inl ⟨hc, E18low.reduction1 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hc hs (hP.q55_strong_rows hv) ht hG14 hS14⟩
  · have hc : cnt8 (facetRows P) = 4 := by omega
    have hs : sumR8 (facetRows P) ≤ 36 := by rw [hc] at hridge; omega
    exact Or.inr (Or.inl ⟨hc, E18low.reduction2 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hc hs (hP.q55_strong_rows hv) ht hG14 hS14⟩)
  · have hc : cnt8 (facetRows P) = 6 := by omega
    have hs : sumR8 (facetRows P) ≤ 60 := by rw [hc] at hridge; omega
    exact Or.inr (Or.inr ⟨hc, E18low.reduction3 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      hpairF hpairS hc hs (hP.q55_strong_rows hv) ht hG14 hS14⟩)

/-- The ridge threshold 64 closes the entire few-full branch. -/
theorem IsCSPolytope5.three_pow_five_16_18_r_ge_sixtyfour
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hr : 64 ≤ (flagDataOf P).r) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_cases hG : 16 ≤ (flagDataOf P).G
  · exact hP.three_pow_five_16_18_G_ge_sixteen hv hh h1 h6 hG
  by_cases hS : 16 ≤ (flagDataOf P).Gs
  · exact hP.three_pow_five_16_18_Gs_ge_sixteen hv hh h1 h6 hS
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hG14 : C.D.G ≤ 14 := by
    obtain ⟨g, hg⟩ := FlagData.even_G C.hD
    change ¬ 16 ≤ C.D.G at hG
    omega
  have hS14 : C.D.Gs ≤ 14 := by
    obtain ⟨s, hs⟩ := C.even_Gs
    change ¬ 16 ≤ C.D.Gs at hS
    omega
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  have hev : Even (cnt8 (facetRows P)) :=
    hP.facetRows_filter_even (fun R => decide (R.n = 8))
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hc : cnt8 (facetRows P) = 2 := by omega
    have hs : sumR8 (facetRows P) ≤ 16 := by rw [hc] at hridge; omega
    exact E18low.leaf_polar_r1_64 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      C.hD.G_nonneg hG14 C.hD.Gs_nonneg hS14 (by exact_mod_cast hr) hc hs
      (hP.q55_strong_rows hv) ht
  · have hc : cnt8 (facetRows P) = 4 := by omega
    have hs : sumR8 (facetRows P) ≤ 36 := by rw [hc] at hridge; omega
    exact E18low.leaf_polar_r2_64 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      C.hD.G_nonneg hG14 C.hD.Gs_nonneg hS14 (by exact_mod_cast hr) hc hs
      (hP.q55_strong_rows hv) ht
  · have hc : cnt8 (facetRows P) = 6 := by omega
    have hs : sumR8 (facetRows P) ≤ 60 := by rw [hc] at hridge; omega
    exact E18low.leaf_polar_r3_64 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
      C.hD.G_nonneg hG14 C.hD.Gs_nonneg hS14 (by exact_mod_cast hr) hc hs
      (hP.q55_strong_rows hv) ht

/-- Both product rows on the polar side are excluded for an actual counterexample. -/
theorem IsCSPolytope5.fewFull18_polar_products_excluded
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (flagDataOf P).r ≤ 62 ∧ qRow ∉ facetRows (polarSet P) ∧
      tRow ∉ facetRows (polarSet P) := by
  have hn : ¬ 64 ≤ (flagDataOf P).r := fun hr =>
    (not_le_of_gt hlt) (hP.three_pow_five_16_18_r_ge_sixtyfour hv hh h1 h6 hr)
  have hr62 : (flagDataOf P).r ≤ 62 := by
    obtain ⟨r, hr⟩ := hP.flagData_valid.even_r
    omega
  have hvS : fvec (polarSet P) 0 = 18 := by
    have := hP.fvec_polar 4 (by norm_num)
    norm_num at this
    rw [this, hh]
  have he := hP.fvec_polar 3 (by norm_num)
  norm_num at he
  refine ⟨hr62, ?_, ?_⟩
  · intro hQ
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hQ
    have hr := hP.polar.edges_ge_72 hvS hF h4 hrow
    rw [he] at hr
    change fvec P 3 ≤ 62 at hr62
    omega
  · intro hT
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hT
    have hr := hP.polar.edges_ge_64_of_tRow hvS hF h4 hrow
    rw [he] at hr
    change fvec P 3 ≤ 62 at hr62
    omega

/-- One full pair forces the single stress cell (0,10) in a counterexample. -/
theorem IsCSPolytope5.fewFull18_one_pair_stresses
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    (flagDataOf P).G = 0 ∧ (flagDataOf P).Gs = 10 := by
  have hres := hP.fewFull18_residual hv hh (by omega) (by omega) hlt
  rcases hres with ⟨_, hm⟩ | ⟨hn, _⟩ | ⟨hn, _⟩
  · simpa only [E18low.remainingCells, List.mem_singleton, Prod.mk.injEq] using hm
  · omega
  · omega

/-- At zero stress, the polar stress must be ten, for every number of full pairs. -/
theorem IsCSPolytope5.fewFull18_zero_stress_polar_ten
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hG : (flagDataOf P).G = 0) :
    (flagDataOf P).Gs = 10 := by
  have hres := hP.fewFull18_residual hv hh h1 h6 hlt
  rcases hres with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩
  all_goals
    simpa [E18low.remainingCells, hG] using hm

/-- The one-full-pair counterexample saturates the elementary incidence bound. -/
theorem IsCSPolytope5.fewFull18_one_pair_incidence
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    (flagDataOf P).I = 128 := by
  obtain ⟨hG, hS⟩ := hP.fewFull18_one_pair_stresses hv hh hc hlt
  have hn : ∀ R ∈ facetRows P, R.n ≤ 8 := fun R hR => by
    have := hP.facetRows_n_le R hR
    omega
  have hi := sum_n_le_seven_length_add_cnt8 (facetRows P) hn
  rw [hP.facetRows_sum_n, hP.facetRows_length, hh, hc] at hi
  have hI128 : (flagDataOf P).I ≤ 128 := hi
  by_contra hne
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hI126 : (C.D.I : ℤ) ≤ 126 := by
    obtain ⟨i, hi⟩ := C.hD.even_I
    change C.D.I ≤ 128 at hI128
    change C.D.I ≠ 128 at hne
    omega
  have hridge := hP.full_ridge_rows hv
  rw [hh, hc] at hridge
  have hs8 : sumR8 (facetRows P) ≤ 16 := by omega
  exact E18low.leaf_onefull_I126 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
    (by change 0 ≤ (flagDataOf P).G; omega) (by change (flagDataOf P).G ≤ 0; omega)
    (by change 10 ≤ (flagDataOf P).Gs; omega) (by change (flagDataOf P).Gs ≤ 10; omega)
    (hP.A_eq_zero_of_G_eq_zero hG) hI126 hc hs8 (hP.q55_strong_rows hv)
    (hP.t_le_of_faces_lt hlt)

/-- In the one-pair residual case every facet has seven or eight vertices. -/
theorem IsCSPolytope5.fewFull18_one_pair_rows_ge_seven
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    ∀ R ∈ facetRows P, 7 ≤ R.n := by
  have hI := hP.fewFull18_one_pair_incidence hv hh hc hlt
  apply seven_le_n_of_incidence_saturated
  · intro R hR
    have := hP.facetRows_n_le R hR
    omega
  · rw [hP.facetRows_sum_n, hP.facetRows_length, hh, hc]
    exact hI

/-- At zero stress, a full row has at least eight ridges: the smaller dual
catalogue leaves only the prism, R35, and R19, all already excluded. -/
theorem IsCSPolytope5.full_row_r_ge_eight_of_G0
    (hv : fvec P 0 = 16) (hG : (flagDataOf P).G = 0)
    (hT : tRow ∉ facetRows P) {R : Row} (hR : R ∈ facetRows P) (hn : R.n = 8) :
    8 ≤ R.r := by
  by_contra hbad
  have hctx := hP.rowOK_P_le (nmax := 8)
    (fun S hS => by have := hP.facetRows_n_le S hS; omega)
    (show ∀ S ∈ facetRows P, S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil) R hR
  have hs := hctx.smalld (by omega)
  have hg : R.g = 0 := by have := hctx.g_le; rw [hG] at this; have := hctx.g_nonneg; omega
  have hcheck : ∀ S ∈ smallRows, S.r = 8 → S.g = 0 →
      S.dual = tRow ∨ S.dual = r35Row ∨ S.dual = zRow := by decide +kernel
  have hgd : R.dual.g = 0 := by
    simp only [Row.dual, Row.g] at hg ⊢
    omega
  have hx := hcheck R.dual hs hn hgd
  rw [Row.dual_dual] at hx
  rcases hx with rfl | rfl | rfl
  · exact hT hR
  · exact hP.r35Row_not_mem_of_G_eq_zero hv hG hR
  · exact hP.zRow_not_mem_of_G_eq_zero hv hG hR

/-- Each full facet in the one-pair residual configuration has eight ridges
and 38 vertex-ridge flags. -/
theorem IsCSPolytope5.fewFull18_one_pair_full_shape
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {R : Row} (hR : R ∈ facetRows P) (hn : R.n = 8) : R.r = 8 ∧ R.J = 38 := by
  obtain ⟨hG, _⟩ := hP.fewFull18_one_pair_stresses hv hh hc hlt
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  have hridge := hP.full_ridge_rows hv
  rw [hh, hc] at hridge
  have hs : sumR8 (facetRows P) ≤ 16 := by omega
  have hr : R.r = 8 := by
    apply r_eq_eight_of_sum_le ((facetRows P).filter fun S => S.n = 8)
    · intro S hS
      simp only [List.mem_filter, decide_eq_true_eq] at hS
      exact hP.full_row_r_ge_eight_of_G0 hv hG hT hS.1 hS.2
    · change sumR8 (facetRows P) ≤ 8 * cnt8 (facetRows P)
      omega
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hR, hn⟩
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hb := (C.rowF R hR).g_le
  have hz := (C.rowF R hR).g_nonneg
  change 2 * R.g ≤ (flagDataOf P).G at hb
  rw [hG] at hb
  simp only [Row.g, hn, hr] at hb hz
  exact ⟨hr, by omega⟩

/-- Only four full rows remain in the one-pair case, before using the global
profile arithmetic. This uses the polygon excess, not an eight-vertex catalogue. -/
theorem IsCSPolytope5.fewFull18_one_pair_full_row_candidates
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {R : Row} (hR : R ∈ facetRows P) (hn : R.n = 8) :
    ∃ k : ℕ, 19 ≤ k ∧ k ≤ 22 ∧ R = ⟨8, k, k, 8, 38⟩ := by
  obtain ⟨hr, hJ⟩ := hP.fewFull18_one_pair_full_shape hv hh hc hlt hR hn
  have hreal := hP.facetRows_real R hR
  have hE := realRow_euler hreal
  have hB := realRow_B4 hreal
  have hX := realRow_polygon_excess hreal
  have hp : R.p = R.e := by omega
  have hEq : R = ⟨R.n, R.e, R.p, R.r, R.J⟩ := rfl
  rw [hn, hp, hr, hJ] at hEq
  have hne : R.e ≠ 18 := by
    intro he
    apply hP.facetRows_not_fake8 R hR
    rw [hEq, he]
    decide +kernel
  exact ⟨R.e, by omega, by omega, hEq⟩

end Kalai5
