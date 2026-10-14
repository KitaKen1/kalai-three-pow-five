# Mathematical target correspondence

The primary declaration is `Kalai.three_pow_five`. Its complete statement
is written in [../Challenge.lean](../Challenge.lean), using only Mathlib.
The theorem in [../Kalai5/FormalConjectures.lean](../Kalai5/FormalConjectures.lean) has the identical signature.

| Natural-language clause | Lean expression |
|---|---|
| Five-dimensional real Euclidean space | `EuclideanSpace ℝ (Fin 5)` |
| A convex polytope | `∃ V : Finset ..., P = convexHull ℝ (V : Set ...)` |
| Full dimension | `(interior P).Nonempty` |
| Symmetry about the origin | `∀ x ∈ P, -x ∈ P` |
| A face | `IsExposed ℝ P F` |
| Exclude the empty face | `F.Nonempty` |
| Count the finite family of faces | `{F : Set ... | F.Nonempty ∧ IsExposed ℝ P F}.ncard` |
| At least 243 faces | `3 ^ 5 ≤ ...` |

For convex polytopes every face is exposed. The zero linear functional
exposes the whole polytope, so that face is included. The finite convex hull
hypothesis makes the face family finite; this is not a count of points in P.
A centrally symmetric polytope with a different center is translated to the
origin without changing its face count.

There is no restriction on the number of generating points, vertices or
facets. No certificate, classification, rigidity theorem, or custom
polytope structure is an extra hypothesis of the public declaration.

The reference has one deliberate proof placeholder and no definition holes.
`FCSolution` imports the proof sources. Comparator checks
the same name, statement and dependent definitions and audits the proof
dependencies against the three permitted axioms.
