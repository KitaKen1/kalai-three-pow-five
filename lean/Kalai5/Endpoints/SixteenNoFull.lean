import Kalai5.Endpoints.E16k.Closure
import Kalai5.Endpoints.TwentyTwenty

/-!
# Endpoints `(16,16)` and `(16,18)` without full facets

`IsCSPolytope5.three_pow_five_16_noFull`: a centrally symmetric 5-polytope with sixteen vertices,
`16` or `18` facets, and no facet with eight vertices (no *full* facet) has at least `243`
nonempty faces.  Every facet row has `n ≤ 7`, so the certificate context has `nF = 7`; then
`E16k.closure16` (one certificate) and `E16k.closure18` (four rectangles and two cells split along
the largest local `g`, with the two-facet stress bound).
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Row facts for the facets of `P` when every facet has at most `nmax` vertices. -/
lemma IsCSPolytope5.rowOK_P_le {nmax : ℕ} (hn : ∀ R ∈ facetRows P, R.n ≤ nmax)
    {excl : List Row} (hex : ∀ R ∈ facetRows P, R ∉ excl) :
    ∀ R ∈ hP.rowsData.rows, RowOK nmax (flagDataOf P).G excl R := by
  intro R hR
  have hW := hP.whiteleyCS_of_w3 alexandrov3_proof
  exact rowOK_of_real Gale.small_classification_proof (hP.facetRows_real R hR) (hn R hR)
    (hP.facet_g_nonneg R hR) (hP.stress_localization_of_whiteley hW R hR) (hex R hR)

/-- The certificate context of a 16-vertex counterexample without full facets. -/
noncomputable def IsCSPolytope5.ctx16k {h nS : ℕ} (hv : fvec P 0 = 16) (hh : fvec P 4 = h)
    (hS : h ≤ 2 * nS) (hn : ∀ R ∈ facetRows P, R.n ≤ 7) : Ctx 16 h 7 nS [] [] :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh, hP.rowOK_P_le hn (fun _ _ => List.not_mem_nil),
    hP.rowOK_S (by omega) (fun _ _ => List.not_mem_nil),
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

/-- **Sixteen vertices, `16` or `18` facets, no full facet**: at least `243` faces. -/
theorem IsCSPolytope5.three_pow_five_16_noFull {h : ℕ} (hv : fvec P 0 = 16)
    (hh : fvec P 4 = h) (h1618 : h = 16 ∨ h = 18) (hn : ∀ R ∈ facetRows P, R.n ≤ 7) :
    243 ≤ (faces P).ncard := by
  by_contra hlt
  push_neg at hlt
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
  rcases h1618 with rfl | rfl
  · exact E16k.closure16 (hP.ctx16k (nS := 8) hv hh (by norm_num) hn) ht'
  · exact E16k.closure18 (hP.ctx16k (nS := 9) hv hh (by norm_num) hn)
      (fun j hj => hP.cntBig_le_two' hj) (fun j hj => hP.cntBig_le_two_polar hj) ht'

end cs

end Kalai5
