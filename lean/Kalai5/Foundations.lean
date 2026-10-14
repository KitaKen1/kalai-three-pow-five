import Kalai5.Statement
import Kalai5.FlagData
import Kalai5.LocalData

/-!
# Face and flag numbers of an actual polytope

Definitions connecting the geometric statement (`Kalai5.Statement`) to the arithmetic layers
(`Kalai5.FlagData`, `Kalai5.LocalData`).  No theorems are proved here; the facts relating these
numbers are collected as obligations in `Kalai5.Obligations`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- Number of flags `F ⊆ G` of nonempty faces with `dim F = i`, `dim G = j`. -/
noncomputable def flag2 (P : Set (E d)) (i j : ℕ) : ℕ :=
  {FG : Set (E d) × Set (E d) | FG.1 ∈ faces P ∧ FG.2 ∈ faces P ∧ FG.1 ⊆ FG.2 ∧
    dim FG.1 = i ∧ dim FG.2 = j}.ncard

/-- Number of flags `F ⊆ G ⊆ H` of nonempty faces with dimensions `i, j, k`. -/
noncomputable def flag3 (P : Set (E d)) (i j k : ℕ) : ℕ :=
  {FGH : Set (E d) × Set (E d) × Set (E d) | FGH.1 ∈ faces P ∧ FGH.2.1 ∈ faces P ∧
    FGH.2.2 ∈ faces P ∧ FGH.1 ⊆ FGH.2.1 ∧ FGH.2.1 ⊆ FGH.2.2 ∧
    dim FGH.1 = i ∧ dim FGH.2.1 = j ∧ dim FGH.2.2 = k}.ncard

/-- The face and flag numbers of a 5-polytope. -/
noncomputable def flagDataOf (P : Set E5) : FlagData where
  v := fvec P 0
  e := fvec P 1
  p := fvec P 2
  r := fvec P 3
  h := fvec P 4
  I := flag2 P 0 4
  x := flag2 P 0 2
  y := flag2 P 2 4
  f03 := flag2 P 0 3
  f13 := flag2 P 1 3
  f14 := flag2 P 1 4
  f024 := flag3 P 0 2 4

/-- Number of `k`-faces of `P` contained in `F`. -/
noncomputable def cnt (P F : Set (E d)) (k : ℕ) : ℕ :=
  {G | G ∈ faces P ∧ G ⊆ F ∧ dim G = k}.ncard

/-- Number of incidences `G ⊆ H ⊆ F` between faces of `P` with `dim G = i`, `dim H = j`. -/
noncomputable def incid (P F : Set (E d)) (i j : ℕ) : ℕ :=
  {GH : Set (E d) × Set (E d) | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧ GH.1 ⊆ GH.2 ∧ GH.2 ⊆ F ∧
    dim GH.1 = i ∧ dim GH.2 = j}.ncard

/-- The row `(n, e, p, r; J)` of a face `F` of `P`. -/
noncomputable def faceRow (P F : Set (E d)) : Row :=
  ⟨cnt P F 0, cnt P F 1, cnt P F 2, cnt P F 3, incid P F 0 3⟩

/-- The row `(n, e, p, r; J)` of a polytope (in any ambient space). -/
noncomputable def rowOf (Q : Set (E d)) : Row :=
  ⟨fvec Q 0, fvec Q 1, fvec Q 2, fvec Q 3, flag2 Q 0 3⟩

/-- `R` is the row of an actual 4-dimensional polytope (in some `ℝᵈ`). -/
def IsRealRow (R : Row) : Prop :=
  ∃ (d : ℕ) (Q : Set (E d)), (∃ V : Finset (E d), Q = convexHull ℝ (V : Set (E d))) ∧
    dim Q = 4 ∧ rowOf Q = R

open Classical in
/-- The facets of `P` in some order (empty if there were infinitely many). -/
noncomputable def facetList (P : Set E5) : List (Set E5) :=
  if h : {F | F ∈ faces P ∧ dim F = 4}.Finite then h.toFinset.toList else []

/-- The rows of all facets of `P`. -/
noncomputable def facetRows (P : Set E5) : List Row := (facetList P).map (faceRow P)

/-- `EndpointClaim a b`: every centrally symmetric 5-polytope with `f₀ = a`, `f₄ = b` has at
least 243 nonempty faces. -/
def EndpointClaim (a b : ℕ) : Prop :=
  ∀ P : Set E5, IsCSPolytope5 P → fvec P 0 = a → fvec P 4 = b → 243 ≤ (faces P).ncard

end Kalai5
