import Kalai5.Endpoints.E1822.Closure
import Kalai5.Endpoints.SixteenTwentyTwo
import Kalai5.FullProd.SideEdges

/-!
# Endpoint `(18,22)`

A counterexample with `18` vertices and `22` facets has `t = f₁ + f₃ ≤ 118`.

* If some facet has the row `qRow = (9,18,15,6; 36)` of `Δ2 × Δ2`, it contains half of the
  vertices and `P` has at least `72` edges (`IsCSPolytope5.edges_ge_72`); every facet has at least
  five ridges, so `2 f₃ ≥ 5 · 22` and `t ≥ 72 + 55 > 118`.
* Otherwise the facet rows of `P` and of its polar satisfy the row facts of the certificate
  engine (`Cert.Engine`), and the case analysis on `(G, G*)` (`E1822.closure`) gives a
  contradiction.
-/

namespace Kalai5

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **The flag numbers of the polar**: `f₀ ↔ f₄`, `f₁ ↔ f₃`, `f₀₂ ↔ f₂₄`, `f₀₃ ↔ f₁₄`. -/
lemma IsCSPolytope5.polarRel : PolarRel (flagDataOf P) (flagDataOf (polarSet P)) := by
  have v := hP.fvec_polar 4 (by norm_num)
  have e := hP.fvec_polar 3 (by norm_num)
  have p := hP.fvec_polar 2 (by norm_num)
  have r := hP.fvec_polar 1 (by norm_num)
  have h := hP.fvec_polar 0 (by norm_num)
  have I := hP.flag2_polar 0 4 (by norm_num) le_rfl
  have x := hP.flag2_polar 2 4 (by norm_num) le_rfl
  have y := hP.flag2_polar 0 2 (by norm_num) (by norm_num)
  have f03 := hP.flag2_polar 1 4 (by norm_num) le_rfl
  have f14 := hP.flag2_polar 0 3 (by norm_num) (by norm_num)
  norm_num at v e p r h I x y f03 f14
  exact ⟨v, e, p, r, h, I, x, y, f03, f14⟩

/-- The polygon excess is self-polar. -/
lemma IsCSPolytope5.A_polar : (flagDataOf (polarSet P)).A = (flagDataOf P).A := by
  have h1 := hP.flagData_valid.f024_eq
  have h2 := hP.polar.flagData_valid.f024_eq
  have rel := hP.polarRel
  simp only [FlagData.A]
  rw [h1, h2, rel.I, rel.x, rel.y, rel.e, rel.r, rel.p]
  ring

/-- `G* = 0` forces `A = 0` (the polygon-star lemma in the polar). -/
lemma IsCSPolytope5.A_eq_zero_of_Gs_eq_zero (hG : (flagDataOf P).Gs = 0) : (flagDataOf P).A = 0 := by
  rw [← hP.A_polar]
  exact hP.polar.A_eq_zero_of_G_eq_zero (by rw [hP.G_polar]; exact hG)

/-- Every facet has at least five ridges: `2 f₃ ≥ 5 f₄`. -/
lemma IsCSPolytope5.five_mul_fvec_four_le : 5 * fvec P 4 ≤ 2 * fvec P 3 := by
  have h5 : ∀ R ∈ facetRows P, (5 : ℤ) ≤ (R.r : ℤ) := fun R hR => by
    exact_mod_cast realRow_five_le_r (hP.facetRows_real R hR)
  have hsum := le_sum_of_forall (fun R => (R.r : ℤ)) h5
  have hcast : ((facetRows P).map fun R => (R.r : ℤ)).sum = (((facetRows P).map Row.r).sum : ℤ) := by
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  have hs : ((facetRows P).map Row.r).sum = 2 * fvec P 3 := hP.rowsData.sum_r
  rw [hcast, hs, hP.facetRows_length] at hsum
  push_cast at hsum
  omega

/-- The facet rows of an `(18,22)` counterexample without a `Δ2 × Δ2` facet. -/
lemma IsCSPolytope5.rowOK_18_22 (hv : fvec P 0 = 18) (hQ : qRow ∉ facetRows P) :
    ∀ R ∈ hP.rowsData.rows, RowOK 9 (flagDataOf P).G [⟨9, 18, 15, 6, 36⟩] R := by
  intro R hR
  have hW := hP.whiteleyCS_of_w3 alexandrov3_proof
  refine rowOK_of_real Gale.small_classification_proof (hP.facetRows_real R hR) ?_
    (hP.facet_g_nonneg R hR) (hP.stress_localization_of_whiteley hW R hR) ?_
  · have := hP.facetRows_n_le R hR
    omega
  · intro hmem
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hQ hR

/-- The facet rows of the polar (the vertex figures of `P`). -/
lemma IsCSPolytope5.rowOK_polar (hh : fvec P 4 = 22) :
    ∀ R ∈ hP.polar.rowsData.rows, RowOK 11 (flagDataOf P).Gs [] R := by
  intro R hR
  have hW := hP.polar.whiteleyCS_of_w3 alexandrov3_proof
  have hg := hP.polar.stress_localization_of_whiteley hW R hR
  rw [hP.G_polar] at hg
  refine rowOK_of_real Gale.small_classification_proof (hP.polar.facetRows_real R hR) ?_
    (hP.polar.facet_g_nonneg R hR) hg (by simp)
  have h1 := hP.polar.facetRows_n_le R hR
  have h2 := hP.fvec_polar 4 (by norm_num)
  norm_num at h2
  rw [h2, hh] at h1
  omega

end cs

/-- **Endpoint `(18,22)`.** -/
theorem endpoint_18_22_proof : EndpointClaim 18 22 := by
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
  by_cases hQ : qRow ∈ facetRows P
  · -- a facet `Δ2 × Δ2`: many edges and ridges
    obtain ⟨F, hF, h4, hrow⟩ := hP.mem_facetRows hQ
    have h72 := hP.edges_ge_72 hv hF h4 hrow
    have h55 := hP.five_mul_fvec_four_le
    rw [hh] at h55
    simp only [FlagData.t, flagDataOf] at ht
    omega
  · exact E1822.closure
      ⟨flagDataOf P, flagDataOf (polarSet P), hD, hP.rowsData, hP.polar.rowsData, hP.polarRel, hv, hh,
        hP.rowOK_18_22 hv hQ, hP.rowOK_polar hh, hP.A_eq_zero_of_G_eq_zero,
        hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even, hP.polar.facetRows_filter_even⟩
      (by exact_mod_cast ht)

end Kalai5
