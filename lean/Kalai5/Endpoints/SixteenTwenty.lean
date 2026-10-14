import Kalai5.Endpoints.Z20.NoFull
import Kalai5.Endpoints.E20f.Closure
import Kalai5.Endpoints.SixteenFew

/-!
# Endpoint `(16,20)` modulo the low-rank claim and rank four with four to six full pairs

* Without a full facet: `IsCSPolytope5.three_pow_five_16_20_noFull` (Z20, the quadrilateral-link
  inequality).
* At least seven full pairs: `IsCSPolytope5.three_pow_five_16_20_manyFull` (certificates
  `Endpoints/E20f`, the count of full facets and the ridge bound; a facet `T = Δ₃ × I` is
  `full_prism`).
* Otherwise `LowRank16 20` (from `FewFull16 20`, one to three full pairs, and the octahedral
  rank-three case) leaves four linearly independent full normals with four to six full pairs:
  `A16Mid20`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

section

variable (hP : IsCSPolytope5 P)
include hP

/-- The certificate context at `(16,20)` with full facets allowed (no facet `T` on `P`). -/
noncomputable def IsCSPolytope5.ctx20f (hv : fvec P 0 = 16) (hh : fvec P 4 = 20)
    (hT : tRow ∉ facetRows P) : Ctx 16 20 8 10 [tRow] [] :=
  ⟨flagDataOf P, flagDataOf (polarSet P), hP.flagData_valid, hP.rowsData, hP.polar.rowsData,
    hP.polarRel, hv, hh,
    hP.rowOK_P_le (nmax := 8) (fun R hR => by have := hP.facetRows_n_le R hR; omega)
      (fun R hR h => hT (by rw [List.mem_singleton] at h; rw [← h]; exact hR)),
    hP.rowOK_S (by omega) (fun _ _ => List.not_mem_nil),
    hP.A_eq_zero_of_G_eq_zero, hP.A_eq_zero_of_Gs_eq_zero, hP.facetRows_filter_even,
    hP.polar.facetRows_filter_even⟩

/-- **Sixteen vertices, twenty facets, at least seven full pairs**: at least `243` faces. -/
theorem IsCSPolytope5.three_pow_five_16_20_manyFull (hv : fvec P 0 = 16) (hh : fvec P 4 = 20)
    (h14 : 14 ≤ cnt8 (facetRows P)) : 243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
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
  set C := hP.ctx20f hv hh hT with hC
  have hev : Even (cnt8 (facetRows P)) := hP.facetRows_filter_even (fun R => decide (R.n = 8))
  have hle : cnt8 (facetRows P) ≤ 20 := by
    have h1 : cnt8 (facetRows P) ≤ (facetRows P).length := List.length_filter_le _ _
    rw [hP.facetRows_length, hh] at h1
    exact h1
  have hridge := hP.full_ridge_rows hv
  rw [hh] at hridge
  obtain ⟨k, hk⟩ := hev
  have hk' : k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  rcases hk' with rfl | rfl | rfl | rfl
  · have hs : sumR8 (facetRows P) ≤ 210 := by rw [hk] at hridge; omega
    exact E20f.closure7 C (by show cnt8 (facetRows P) = 14; omega) hs ht'
  · have hs : sumR8 (facetRows P) ≤ 256 := by rw [hk] at hridge; omega
    exact E20f.closure8 C (by show cnt8 (facetRows P) = 16; omega) hs ht'
  · have hs : sumR8 (facetRows P) ≤ 306 := by rw [hk] at hridge; omega
    exact E20f.closure9 C (by show cnt8 (facetRows P) = 18; omega) hs ht'
  · have hs : sumR8 (facetRows P) ≤ 360 := by rw [hk] at hridge; omega
    exact E20f.closure10 C (by show cnt8 (facetRows P) = 20; omega) hs ht'

end

/-- **Rank four with four to six full pairs at twenty facets**: sixteen vertices, twenty facets,
at most twelve facets with eight vertices and four linearly independent full normals give at
least `243` faces. -/
def A16Mid20 : Prop :=
  ∀ P : Set E5, IsCSPolytope5 P → fvec P 0 = 16 → fvec P 4 = 20 → cnt8 (facetRows P) ≤ 12 →
    ∀ u : Fin 4 → E5, LinearIndependent ℝ u →
      (∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1) → 243 ≤ (faces P).ncard

/-- **Sixteen vertices, twenty facets**, from the low-rank claim and rank four with four to six
full pairs. -/
theorem IsCSPolytope5.three_pow_five_16_20 (hL : LowRank16 20) (hA : A16Mid20)
    (hP : IsCSPolytope5 P) (hv : fvec P 0 = 16) (hh : fvec P 4 = 20) : 243 ≤ (faces P).ncard := by
  by_cases hn : ∀ R ∈ facetRows P, R.n ≤ 7
  · exact hP.three_pow_five_16_20_noFull hv hh hn
  push Not at hn
  obtain ⟨R, hR, hR8⟩ := hn
  have hR8' : R.n = 8 := by
    have := hP.facetRows_n_le R hR
    omega
  rcases hL P hP hv hh ⟨R, hR, hR8'⟩ with ⟨w, hw, hwf⟩ | h243
  · by_cases h12 : cnt8 (facetRows P) ≤ 12
    · exact hA P hP hv hh h12 w hw hwf
    · obtain ⟨k, hk⟩ := hP.facetRows_filter_even (fun R => decide (R.n = 8))
      have hk' : cnt8 (facetRows P) = k + k := hk
      exact hP.three_pow_five_16_20_manyFull hv hh (by omega)
  · exact h243

end Kalai5
