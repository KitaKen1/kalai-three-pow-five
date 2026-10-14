import Kalai5.Endpoints.E1820.Closure
import Kalai5.Endpoints.TwentyTwenty
import Kalai5.FullProd.QF20b
import Kalai5.FullProd.TF18d

/-!
# Endpoint `(18,20)`

A counterexample with `18` vertices and `20` facets has `t = f₁ + f₃ ≤ 118`.

* A facet of row `qRow` (`Δ2 × Δ2`): `e ≥ 72` (`edges_ge_72`) and `2 f₃ ≥ 5 f₄ = 100`.
* Otherwise, a facet of the polar of row `qRow`: the polar has twenty vertices, so `r ≥ 66`
  (`edges_ge_66_of_qRow`); one certificate (`E1820.closure2`).
* Otherwise, a facet of row `tRow` (`Δ1 × Δ3`): `e ≥ 60` (`edges_ge_60_of_tRow`); three cells
  (`E1820.closure3`).
* Otherwise `qRow` is excluded on both sides and `tRow` on `P` (`E1820.closure4`).
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The certificate context of an `(18,20)` counterexample. -/
noncomputable def IsCSPolytope5.ctx1820 (hv : fvec P 0 = 18) (hh : fvec P 4 = 20)
    {excl exclS : List Row} (hex : ∀ R ∈ facetRows P, R ∉ excl)
    (hexS : ∀ R ∈ facetRows (polarSet P), R ∉ exclS) : Ctx 18 20 9 10 excl exclS :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh, hP.rowOK_P (by omega) hex, hP.rowOK_S (by omega) hexS,
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

end cs

/-- **Endpoint `(18,20)`.** -/
theorem endpoint_18_20_proof : EndpointClaim 18 20 := by
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
  by_cases hQ : qRow ∈ facetRows P
  · -- a facet `Δ2 × Δ2`: many edges and ridges
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hQ
    have h72 := hP.edges_ge_72 hv hF h4 hrow
    have h55 := hP.five_mul_fvec_four_le
    rw [hh] at h55
    simp only [FlagData.t, flagDataOf] at ht
    omega
  have hexQ : ∀ R ∈ facetRows P, R ∉ [⟨9, 18, 15, 6, 36⟩] := by
    intro R hR hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hQ hR
  by_cases hQs : qRow ∈ facetRows (polarSet P)
  · -- a vertex figure `Δ2 ⊕ Δ2`: the polar has twenty vertices
    obtain ⟨F, hF, h4, hrow⟩ := hP.polar.mem_facetRows hQs
    have hvS : fvec (polarSet P) 0 = 20 := by
      have := hP.fvec_polar 4 (by norm_num)
      norm_num at this
      rw [this, hh]
    have hr := hP.polar.edges_ge_66_of_qRow hvS hF h4 hrow
    have e3 := hP.fvec_polar 3 (by norm_num)
    norm_num at e3
    rw [e3] at hr
    exact E1820.closure2 (hP.ctx1820 hv hh hexQ (hnil _)) (by exact_mod_cast hr) ht'
  have hexQs : ∀ R ∈ facetRows (polarSet P), R ∉ [⟨9, 18, 15, 6, 36⟩] := by
    intro R hR hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hQs hR
  by_cases hT : tRow ∈ facetRows P
  · -- a facet `Δ1 × Δ3`
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hT
    have he := hP.edges_ge_60_of_tRow hv hF h4 hrow
    exact E1820.closure3 (hP.ctx1820 hv hh hexQ hexQs) (by exact_mod_cast he) ht'
  · have hexQT : ∀ R ∈ facetRows P, R ∉ [⟨9, 18, 15, 6, 36⟩, ⟨8, 16, 14, 6, 32⟩] := by
      intro R hR hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hQ hR
      · exact hT hR
    exact E1820.closure4 (hP.ctx1820 hv hh hexQT hexQs) ht'

end Kalai5
