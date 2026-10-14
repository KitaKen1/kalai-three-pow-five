import Kalai5.Endpoints.E16f.Closure
import Kalai5.Endpoints.SixteenNoFull
import Kalai5.FullPrism.Final
import Kalai5.Endpoints.SixteenRank

/-!
# Endpoint `(16,16)` with one to three full pairs

`IsCSPolytope5.three_pow_five_16_16_fewFull`: sixteen vertices, sixteen facets, and between two
and six facets with eight vertices give at least `243` faces.  A facet `T = Δ₃ × I` on either side
is `full_prism` (on the polar: sixteen vertices, sixteen facets); otherwise the certificate context
`Ctx 16 16 8 8 [tRow] [tRow]` with the number of full facets `2 kP` and the ridge count
(`full_ridge_rows`) closes by `E16f.closure1/2/3`.
-/

namespace Kalai5

variable {P : Set E5}

section

variable (hP : IsCSPolytope5 P)
include hP

/-- The certificate context with full facets allowed (no facet `T` on either side). -/
noncomputable def IsCSPolytope5.ctx16f (hv : fvec P 0 = 16) (hh : fvec P 4 = 16)
    (hT : tRow ∉ facetRows P) (hTs : tRow ∉ facetRows (polarSet P)) :
    Ctx 16 16 8 8 [tRow] [tRow] :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh,
    hP.rowOK_P_le (nmax := 8) (fun R hR => by have := hP.facetRows_n_le R hR; omega)
      (fun R hR h => hT (by rw [List.mem_singleton] at h; rw [← h]; exact hR)),
    hP.rowOK_S (by omega) (fun R hR h => hTs (by rw [List.mem_singleton] at h; rw [← h]; exact hR)),
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

/-- **Sixteen vertices, sixteen facets, one to three full pairs**: at least `243` faces. -/
theorem IsCSPolytope5.three_pow_five_16_16_fewFull (hv : fvec P 0 = 16) (hh : fvec P 4 = 16)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_cases hTs : tRow ∈ facetRows (polarSet P)
  · have hv' : fvec (polarSet P) 0 = 16 := by
      have := hP.fvec_polar 4 le_rfl
      simp only [Nat.sub_self] at this
      rw [this, hh]
    have := hP.polar.full_prism hv' hTs
    rwa [hP.faces_ncard_polar] at this
  by_contra hlt
  push Not at hlt
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    exact hlt
  have ht : (flagDataOf P).t ≤ 118 := by
    by_contra h
    exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
  have ht' : ((flagDataOf P).t : ℤ) ≤ 118 := by exact_mod_cast ht
  set C := hP.ctx16f hv hh hT hTs with hC
  have hev : Even (cnt8 (facetRows P)) := hP.facetRows_filter_even (fun R => decide (R.n = 8))
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  have hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2 :=
    fun j hj => hP.cntBig_le_two' hj
  have hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2 :=
    fun j hj => hP.cntBig_le_two_polar hj
  obtain ⟨k, hk⟩ := hev
  have hk3 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl
  · have hs : sumR8 (facetRows P) ≤ 14 := by rw [hk] at hridge; omega
    exact E16f.closure1 C (by show cnt8 (facetRows P) = 2; omega) hs ht'
  · have hs : sumR8 (facetRows P) ≤ 32 := by rw [hk] at hridge; omega
    exact E16f.closure2 C (by show cnt8 (facetRows P) = 4; omega) hs ht'
  · have hs : sumR8 (facetRows P) ≤ 54 := by rw [hk] at hridge; omega
    exact E16f.closure3 C hpairF hpairS (by show cnt8 (facetRows P) = 6; omega) hs ht'

end

/-- **`FewFull16 16`**: sixteen facets. -/
theorem fewFull16_16 : FewFull16 16 := fun _ hP hv hh h1 h6 =>
  hP.three_pow_five_16_16_fewFull hv hh h1 h6

end Kalai5
