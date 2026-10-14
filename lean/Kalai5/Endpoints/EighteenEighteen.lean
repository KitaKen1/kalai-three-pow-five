import Kalai5.Endpoints.E1818.Closure
import Kalai5.Endpoints.EighteenTwenty
import Kalai5.Endpoints.NoU
import Kalai5.FullProd.TF18g

/-!
# Endpoint `(18,18)`

A counterexample with `18` vertices and `18` facets has `t = f₁ + f₃ ≤ 118`; its polar is again
such a counterexample.

* A facet of row `qRow` (`Δ2 × Δ2`): `e ≥ 72` (`edges_ge_72`, `E1818.closure1`); on the polar
  only: `r ≥ 72` (`E1818.closure2`).
* Otherwise a facet of row `tRow` (`Δ1 × Δ3`): `e ≥ 64` (`edges_ge_64_of_tRow`,
  `E1818.closure3`); on the polar only: `r ≥ 64` (`E1818.closure4`).
* Otherwise `qRow`, `tRow` and `u9Row` (`noU1818`) are excluded on both sides, and the two-facet
  stress bound (`cntBig_le_two`) closes the case (`E1818.closure5`).
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The certificate context of an `(18,18)` counterexample. -/
noncomputable def IsCSPolytope5.ctx1818 (hv : fvec P 0 = 18) (hh : fvec P 4 = 18)
    {excl exclS : List Row} (hex : ∀ R ∈ facetRows P, R ∉ excl)
    (hexS : ∀ R ∈ facetRows (polarSet P), R ∉ exclS) : Ctx 18 18 9 9 excl exclS :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh, hP.rowOK_P (by omega) hex, hP.rowOK_S (by omega) hexS,
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

end cs

/-- **Endpoint `(18,18)`**, given the exclusion of the facet `U`. -/
theorem endpoint_18_18_proof : EndpointClaim 18 18 := by
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
  -- the polar is again an `(18,18)` polytope
  have hvS : fvec (polarSet P) 0 = 18 := by
    have := hP.fvec_polar 4 (by norm_num)
    norm_num at this
    rw [this, hh]
  have hhS : fvec (polarSet P) 4 = 18 := by
    have := hP.fvec_polar 0 (by norm_num)
    norm_num at this
    rw [this, hv]
  have e1 := hP.fvec_polar 3 (by norm_num)
  norm_num at e1
  by_cases hQ : qRow ∈ facetRows P
  · -- a facet `Δ2 × Δ2`
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hQ
    have h72 := hP.edges_ge_72 hv hF h4 hrow
    exact E1818.closure1 (hP.ctx1818 hv hh (hnil _) (hnil _)) (by exact_mod_cast h72) ht'
  have hexQ : ∀ R ∈ facetRows P, R ∉ [⟨9, 18, 15, 6, 36⟩] := by
    intro R hR hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hQ hR
  by_cases hQs : qRow ∈ facetRows (polarSet P)
  · -- a vertex figure `Δ2 ⊕ Δ2`
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hQs
    have hr := hP.polar.edges_ge_72 hvS hF h4 hrow
    rw [e1] at hr
    exact E1818.closure2 (hP.ctx1818 hv hh hexQ (hnil _)) (by exact_mod_cast hr) ht'
  have hexQs : ∀ R ∈ facetRows (polarSet P), R ∉ [⟨9, 18, 15, 6, 36⟩] := by
    intro R hR hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hQs hR
  by_cases hT : tRow ∈ facetRows P
  · -- a facet `Δ1 × Δ3`
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hT
    have he := hP.edges_ge_64_of_tRow hv hF h4 hrow
    exact E1818.closure3 (hP.ctx1818 hv hh hexQ hexQs) (by exact_mod_cast he) ht'
  have hexQT : ∀ R ∈ facetRows P, R ∉ [⟨9, 18, 15, 6, 36⟩, ⟨8, 16, 14, 6, 32⟩] := by
    intro R hR hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hQ hR
    · exact hT hR
  by_cases hTs : tRow ∈ facetRows (polarSet P)
  · -- a vertex figure dual to `Δ1 × Δ3`
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hTs
    have hr := hP.polar.edges_ge_64_of_tRow hvS hF h4 hrow
    rw [e1] at hr
    exact E1818.closure4 (hP.ctx1818 hv hh hexQT hexQs) (by exact_mod_cast hr) ht'
  -- none of `Δ2 × Δ2`, `Δ1 × Δ3`, `U` on either side
  have hU := noU1818 P hP hv hh
  have hUs := noU1818 _ hP.polar hvS hhS
  have hexF : ∀ R ∈ facetRows P,
      R ∉ [⟨9, 18, 15, 6, 36⟩, ⟨8, 16, 14, 6, 32⟩, ⟨9, 19, 17, 7, 38⟩] := by
    intro R hR hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hQ hR
    · exact hT hR
    · exact hU hR
  have hexS : ∀ R ∈ facetRows (polarSet P),
      R ∉ [⟨9, 18, 15, 6, 36⟩, ⟨8, 16, 14, 6, 32⟩, ⟨9, 19, 17, 7, 38⟩] := by
    intro R hR hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hQs hR
    · exact hTs hR
    · exact hUs hR
  exact E1818.closure5 (hP.ctx1818 hv hh hexF hexS) (fun j hj => hP.cntBig_le_two' hj)
    (fun j hj => hP.cntBig_le_two_polar hj) ht'

end Kalai5
