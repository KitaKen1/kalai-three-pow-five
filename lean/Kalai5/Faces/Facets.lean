import Kalai5.Faces.Counting
import Kalai5.Faces.Transitive

/-!
# Facets are 4-polytopes

Every facet `F` of a centrally symmetric 5-polytope is itself a 4-dimensional polytope whose own
row equals `faceRow P F`; so every row in `facetRows P` is the row of an actual 4-polytope.
-/

namespace Kalai5

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.facetRows_real : ∀ R ∈ facetRows P, IsRealRow R := by
  classical
  intro R hR
  obtain ⟨F, hF, hd, rfl⟩ := hP.mem_facetRows hR
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  refine ⟨5, F, ⟨V.filter (· ∈ F), face_eq_convexHull_filter hF'⟩, hd, ?_⟩
  rw [rowOf_face hF', ← hV]

end Kalai5
