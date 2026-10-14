/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Kalai's three-to-the-d conjecture and dimension-restricted variants

Kalai's Conjecture A asserts that every centrally symmetric `d`-polytope has
at least `3^d` nonempty faces. The general conjecture remains open.

Sanyal, Werner and Ziegler [SWZ09, Theorem 1.1] established the bound for
`d ≤ 4`. The dimension-five variant has an external Lean proof in this
project. The unrestricted variant for `d ≥ 6` remains open; special classes
of polytopes in those dimensions are not excluded by this statement.

All four statements concern Conjecture A, not Conjectures B or C.
Polytopes are finite convex hulls in Euclidean `d`-space. Full dimension and
symmetry about the origin are explicit hypotheses. The nonempty exposed
faces include the polytope itself. Dimension zero is allowed; its bound is
the elementary `3^0 = 1` case.

*Reference:*
- [SWZ09] R. Sanyal, A. Werner, G. M. Ziegler, *On Kalai's conjectures
  concerning centrally symmetric polytopes*, Discrete Comput. Geom. 41
  (2009), 183–198, [arXiv:0708.3661](https://arxiv.org/abs/0708.3661),
  Conjecture A and Theorem 1.1.

Submission draft: the dimension-five formal_proof link identifies the prior
verified proof archive at an immutable commit. The new publication candidate's
Comparator and private/public CI are pending. The low-dimensional solved tag
refers to [SWZ09]; no external Lean proof for that variant is claimed here.
-/

@[expose] public section

namespace Kalai

/-- Conjecture A in [SWZ09]: every centrally symmetric `d`-polytope has
at least `3^d` nonempty faces, including the polytope itself. -/
@[category research open, AMS 52]
theorem three_pow
    (d : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- The dimension-at-most-four variant, proved in [SWZ09, Theorem 1.1].
The zero-dimensional case is immediate. -/
@[category research solved, AMS 52]
theorem three_pow_le_four
    (d : ℕ) (hd : d ≤ 4)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- The dimension-five variant of Conjecture A, with an external Lean proof.
The declaration name and signature agree exactly with the proved target. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/KitaKen1/kalai-three-pow-five-lean/blob/cb4d4c0db7a51ec92989a4fdf75bfbf12db43679/lean/fast/KalaiFast.lean#L925"]
theorem three_pow_five
    (P : Set (EuclideanSpace ℝ (Fin 5)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin 5)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 5))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ 5 ≤ {F : Set (EuclideanSpace ℝ (Fin 5)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

/-- The remaining dimension-at-least-six variant of Conjecture A. -/
@[category research open, AMS 52]
theorem three_pow_ge_six
    (d : ℕ) (hd : 6 ≤ d)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin d)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin d))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ d ≤ {F : Set (EuclideanSpace ℝ (Fin d)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard := by
  sorry

end Kalai
