import Kalai5.LemmaA.Main
import Kalai5.LemmaA.Geom
import Kalai5.Full.Normals

/-!
# Lemma A

* `IsCSPolytope5.lemmaA`: a centrally symmetric 5-polytope with fourteen vertices and four linearly
  independent full normals has at least 243 nonempty faces.
* `IsCSPolytope5.three_pow_five_of_nine_full`: at fourteen vertices, nine facets with seven
  vertices suffice (they give four independent full normals).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {P : Set E5}

/-- **Lemma A** (bundle `kalai5/lifting_rank4_14.md`): fourteen vertices and four linearly
independent full normals give at least 243 faces. -/
theorem IsCSPolytope5.lemmaA (hP : IsCSPolytope5 P) (h14 : fvec P 0 = 14) {u : Fin 4 → E5}
    (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1) :
    243 ≤ (faces P).ncard :=
  hP.lemmaA_of_core (fun _ hq hinj hfib hspan => LemmaA.lemmaA_core hq hinj hfib hspan) h14 hu
    hfull

/-- At fourteen vertices, nine facets with seven vertices give at least 243 faces. -/
theorem IsCSPolytope5.three_pow_five_of_nine_full (hP : IsCSPolytope5 P) (h14 : fvec P 0 = 14)
    (h9 : 9 ≤ ((facetRows P).filter fun R => R.n = 7).length) : 243 ≤ (faces P).ncard := by
  obtain ⟨u, hu, hfull⟩ := hP.exists_indep_full_normals h14 h9
  exact hP.lemmaA h14 hu hfull

end Kalai5
