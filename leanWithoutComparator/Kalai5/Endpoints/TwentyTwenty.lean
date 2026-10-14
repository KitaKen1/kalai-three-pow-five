import Kalai5.Endpoints.E2020.Closure
import Kalai5.Endpoints.EighteenTwentyTwo
import Kalai5.FullProd.QF20

/-!
# Endpoint `(20,20)`

A counterexample with `20` vertices and `20` facets has `t = f₁ + f₃ ≤ 118`.

* If some facet has the row `qRow = (9,18,15,6; 36)` of `Δ2 × Δ2`, then `e ≥ 62`
  (`IsCSPolytope5.edges_ge_62_of_qRow`: the side edges blocked by the extra pair `±z` are paid
  for by edges at `z`), and one certificate closes the case (`E2020.closureA`).
* If some facet of the polar has the row `qRow`, the same theorem for the polar gives `r ≥ 62`
  (`E2020.closureB`).
* Otherwise the row `qRow` is excluded on both sides and five certificates close the case
  (`E2020.closureC`).
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Row facts for the facets of `P`, with an exclusion list. -/
lemma IsCSPolytope5.rowOK_P {nmax : ℕ} (hn : fvec P 0 ≤ 2 * nmax) {excl : List Row}
    (hex : ∀ R ∈ facetRows P, R ∉ excl) :
    ∀ R ∈ hP.rowsData.rows, RowOK nmax (flagDataOf P).G excl R := by
  intro R hR
  have hW := hP.whiteleyCS_of_w3 alexandrov3_proof
  refine rowOK_of_real Gale.small_classification_proof (hP.facetRows_real R hR) ?_
    (hP.facet_g_nonneg R hR) (hP.stress_localization_of_whiteley hW R hR) (hex R hR)
  have := hP.facetRows_n_le R hR
  omega

/-- Row facts for the facets of the polar, with an exclusion list. -/
lemma IsCSPolytope5.rowOK_S {nmax : ℕ} (hn : fvec P 4 ≤ 2 * nmax) {excl : List Row}
    (hex : ∀ R ∈ facetRows (polarSet P), R ∉ excl) :
    ∀ R ∈ hP.polar.rowsData.rows, RowOK nmax (flagDataOf P).Gs excl R := by
  intro R hR
  have hW := hP.polar.whiteleyCS_of_w3 alexandrov3_proof
  have hg := hP.polar.stress_localization_of_whiteley hW R hR
  rw [hP.G_polar] at hg
  refine rowOK_of_real Gale.small_classification_proof (hP.polar.facetRows_real R hR) ?_
    (hP.polar.facet_g_nonneg R hR) hg (hex R hR)
  have h1 := hP.polar.facetRows_n_le R hR
  have h2 := hP.fvec_polar 4 (by norm_num)
  norm_num at h2
  rw [h2] at h1
  omega

/-- The certificate context of an `(20,20)` counterexample. -/
noncomputable def IsCSPolytope5.ctx2020 (hv : fvec P 0 = 20) (hh : fvec P 4 = 20) {excl exclS : List Row}
    (hex : ∀ R ∈ facetRows P, R ∉ excl) (hexS : ∀ R ∈ facetRows (polarSet P), R ∉ exclS) :
    Ctx 20 20 10 10 excl exclS :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh, hP.rowOK_P (by omega) hex, hP.rowOK_S (by omega) hexS,
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

end cs

/-- **Endpoint `(20,20)`.** -/
theorem endpoint_20_20_proof : EndpointClaim 20 20 := by
  intro P hP hv hh
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
  have hnil : ∀ (L : List Row), ∀ R ∈ L, R ∉ ([] : List Row) := fun _ _ _ => List.not_mem_nil
  by_cases hA : qRow ∈ facetRows P
  · -- a facet `Δ2 × Δ2`
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hA
    have he := hP.edges_ge_62_of_qRow hv hF h4 hrow
    exact E2020.closureA (hP.ctx2020 hv hh (hnil _) (hnil _)) (by exact_mod_cast he) ht'
  by_cases hB : qRow ∈ facetRows (polarSet P)
  · -- a vertex figure `Δ2 ⊕ Δ2`
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hB
    have hvS : fvec (polarSet P) 0 = 20 := by
      have := hP.fvec_polar 4 (by norm_num)
      norm_num at this
      rw [this, hh]
    have hr := hP.polar.edges_ge_62_of_qRow hvS hF h4 hrow
    have e3 := hP.fvec_polar 3 (by norm_num)
    norm_num at e3
    rw [e3] at hr
    exact E2020.closureB (hP.ctx2020 hv hh (hnil _) (hnil _)) (by exact_mod_cast hr) ht'
  · -- no `Δ2 × Δ2` on either side
    have hex : ∀ R ∈ facetRows P, R ∉ [⟨9, 18, 15, 6, 36⟩] := by
      intro R hR hmem
      rw [List.mem_singleton] at hmem
      subst hmem
      exact hA hR
    have hexS : ∀ R ∈ facetRows (polarSet P), R ∉ [⟨9, 18, 15, 6, 36⟩] := by
      intro R hR hmem
      rw [List.mem_singleton] at hmem
      subst hmem
      exact hB hR
    exact E2020.closureC (hP.ctx2020 hv hh hex hexS) ht'

end Kalai5
