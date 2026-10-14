import Kalai5.Cube5.Core
import Kalai5.Cube5.Scans
import Kalai5.Cube5.Certs

/-!
# Cube polytopes in dimension five have at least `243` faces

`cube_faces`: eight points `y_v ∈ {±1}⁵` such that the sixteen points `±y_v` are distinct and
span `ℝ⁵` have at least `243` nonempty faces in their convex hull.  The reduction is `core`; the
table scans (`scans`) and the certificates of the `25` representatives (`certs_ok`) are checked by
the kernel.
-/

namespace Kalai5.Cube5

open Set Kalai5.FullPrism

/-- **Cube polytopes in dimension five.** -/
theorem cube_faces {y : Fin 8 → E5} (hq : ∀ v (j : Fin 5), y v j = 1 ∨ y v j = -1)
    (hinj : Function.Injective (pm16 y))
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm16 y), φ x = 0) → φ = 0) :
    243 ≤ (faces (convexHull ℝ (range (pm16 y)))).ncard :=
  core reps certs certs_ok (cover_of_scans scans) hq hinj hspan

end Kalai5.Cube5
