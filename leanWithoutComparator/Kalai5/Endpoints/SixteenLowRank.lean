import Kalai5.Endpoints.SixteenNoFull
import Kalai5.A16.Main

/-!
# Endpoints `(16,16)` and `(16,18)` modulo the low-rank claim

Without a full facet (every facet row has `n ≤ 7`) this is `three_pow_five_16_noFull`.  A facet
with eight vertices at sixteen vertices is full, so there is a full normal; `LowRank16` (four
linearly independent full normals as soon as `f₄ ≤ 18`) then reduces to the rank-4 case `a16`
(which contains rank 5 through `cube_of_five_full`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- **Low rank.**  A centrally symmetric 5-polytope with sixteen vertices, `h` facets
and a facet with eight vertices (a full facet) has four linearly independent full normals, or at
least `243` faces (the full normals cannot span at most three dimensions without one of the
two). -/
def LowRank16 (h : ℕ) : Prop :=
  ∀ P : Set E5, IsCSPolytope5 P → fvec P 0 = 16 → fvec P 4 = h →
    (∃ R ∈ facetRows P, R.n = 8) →
    (∃ u : Fin 4 → E5, LinearIndependent ℝ u ∧
      ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1) ∨ 243 ≤ (faces P).ncard

/-- **Sixteen vertices, `16` or `18` facets**, from the low-rank claim. -/
theorem IsCSPolytope5.three_pow_five_16_of_lowRank {h : ℕ} (hL : LowRank16 h) {P : Set E5}
    (hP : IsCSPolytope5 P) (hv : fvec P 0 = 16) (hh : fvec P 4 = h)
    (h1618 : h = 16 ∨ h = 18) : 243 ≤ (faces P).ncard := by
  by_cases hn : ∀ R ∈ facetRows P, R.n ≤ 7
  · exact hP.three_pow_five_16_noFull hv hh h1618 hn
  push Not at hn
  obtain ⟨R, hR, hR8⟩ := hn
  have hR8' : R.n = 8 := by
    have := hP.facetRows_n_le R hR
    omega
  rcases hL P hP hv hh ⟨R, hR, hR8'⟩ with ⟨w, hw, hwf⟩ | h243
  · exact hP.a16 hv hw hwf (by omega)
  · exact h243

end Kalai5
