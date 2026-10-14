import Kalai5.Stubs

/-!
# Proposed Formal Conjectures target: Kalai's bound in dimension five

The statement uses only Mathlib definitions. It is repeated verbatim in
`FClikelean/Kalai.lean`; the internal `IsCSPolytope5` structure is not an
additional hypothesis of the public theorem.
-/

namespace Kalai

/-- A full-dimensional, origin-symmetric five-dimensional polytope has at
least `3^5` nonempty faces, including the polytope itself. -/
theorem three_pow_five
    (P : Set (EuclideanSpace ℝ (Fin 5)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin 5)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 5))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ 5 ≤ {F : Set (EuclideanSpace ℝ (Fin 5)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  exact Kalai5.kalai_three_pow_five P
    { polytope := hpoly, full := hfull, symm := hsymm }

end Kalai
