import Kalai5.Polar.Relative

/-!
# Facet and vertex-figure profiles of a polytope

For a 4-polytope `K`, the **facet profile** counts the 3-faces `G` by their face numbers
`triBelow K G = (f₀, f₁, f₂)`, and the **vertex profile** counts the vertices `v` by the face
numbers of their vertex figures, `triAbove K v = (#edges ∋ v, #2-faces ∋ v, #3-faces ∋ v)`.
Both are recorded over the list `fv7` of the f-vectors of 3-polytopes with at most six vertices
(the facets and the vertex figures of a 4-polytope with at most seven vertices).
-/

namespace Kalai5

variable {d : ℕ}

/-- The f-vectors `(f₀, f₁, f₂)` of the 3-polytopes with at most six vertices. -/
def fv7 : List (ℕ × ℕ × ℕ) :=
  [(4, 6, 4), (5, 8, 5), (5, 9, 6), (6, 9, 5), (6, 10, 6), (6, 11, 7), (6, 12, 8)]

/-- Vertices, edges and 2-faces of `K` inside `G`. -/
noncomputable def triBelow (K G : Set (E d)) : ℕ × ℕ × ℕ := (cnt K G 0, cnt K G 1, cnt K G 2)

/-- Edges, 2-faces and 3-faces of `K` containing `G`. -/
noncomputable def triAbove (K G : Set (E d)) : ℕ × ℕ × ℕ := (upIn K G 1, upIn K G 2, upIn K G 3)

/-- Number of 3-faces `G` of `K` with `triBelow K G = t`. -/
noncomputable def facetCnt (K : Set (E d)) (t : ℕ × ℕ × ℕ) : ℕ :=
  {G | G ∈ faces K ∧ dim G = 3 ∧ triBelow K G = t}.ncard

/-- Number of vertices `v` of `K` with `triAbove K v = t`. -/
noncomputable def vertCnt (K : Set (E d)) (t : ℕ × ℕ × ℕ) : ℕ :=
  {G | G ∈ faces K ∧ dim G = 0 ∧ triAbove K G = t}.ncard

/-- The **extended row**: the row, the facet profile and the vertex profile over `fv7`. -/
noncomputable def rowXOf (Q : Set (E d)) : Row × List ℕ × List ℕ :=
  (rowOf Q, fv7.map (facetCnt Q), fv7.map (vertCnt Q))

/-- `X` is the extended row of an actual 4-dimensional polytope (in some `ℝᵈ`). -/
def IsRealRowX (X : Row × List ℕ × List ℕ) : Prop :=
  ∃ (d : ℕ) (Q : Set (E d)), (∃ V : Finset (E d), Q = convexHull ℝ (V : Set (E d))) ∧
    dim Q = 4 ∧ rowXOf Q = X

end Kalai5
