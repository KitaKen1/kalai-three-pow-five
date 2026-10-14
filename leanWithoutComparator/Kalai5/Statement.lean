import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Kalai's `3^d` conjecture in dimension five: the target statement

This file freezes the statement that the whole development aims at.

* A *face* of `P` is a nonempty exposed subset (`IsExposed`).  For polytopes every face is
  exposed, and `P` itself is exposed by the zero functional, so `faces P` is exactly the set of
  nonempty faces of `P`, including `P`.
* `IsCSPolytope5 P` says that `P` is the convex hull of a finite set, has nonempty interior and is
  symmetric about the origin (every centrally symmetric polytope can be translated to this form).
-/

namespace Kalai5

open Set

/-- Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The ambient space `ℝ⁵`. -/
abbrev E5 := E 5

variable {d : ℕ}

/-- Nonempty faces of `P`, including `P` itself. -/
def faces (P : Set (E d)) : Set (Set (E d)) := {F | F.Nonempty ∧ IsExposed ℝ P F}

/-- The dimension of (the affine hull of) a set. -/
noncomputable def dim (F : Set (E d)) : ℕ := Module.finrank ℝ (vectorSpan ℝ F)

/-- `fvec P k` is the number of `k`-dimensional nonempty faces of `P`. -/
noncomputable def fvec (P : Set (E d)) (k : ℕ) : ℕ := {F | F ∈ faces P ∧ dim F = k}.ncard

/-- A full-dimensional convex polytope in `ℝᵈ`. -/
structure IsPolytope (P : Set (E d)) : Prop where
  polytope : ∃ V : Finset (E d), P = convexHull ℝ (V : Set (E d))
  full : (interior P).Nonempty

/-- A full-dimensional convex polytope in `ℝ⁵`, centrally symmetric about the origin. -/
structure IsCSPolytope5 (P : Set E5) : Prop extends IsPolytope P where
  symm : ∀ x ∈ P, -x ∈ P

/-- **Kalai's `3^d` conjecture for `d = 5`.** -/
def MainClaim : Prop := ∀ P : Set E5, IsCSPolytope5 P → 243 ≤ (faces P).ncard

/-- Sanity check of the convention: `P` itself is counted among its faces. -/
lemma self_mem_faces {P : Set (E d)} (hP : P.Nonempty) : P ∈ faces P :=
  ⟨hP, IsExposed.refl P⟩

end Kalai5
