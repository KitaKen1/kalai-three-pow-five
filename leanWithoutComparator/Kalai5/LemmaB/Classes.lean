import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Functor
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.SProd
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic

/-!
# Lemma B: three full normals of rank three see only three classes

Let `Q ⊆ {±1}³` be the set of "positions" `q(x) = (u₁(x), u₂(x), u₃(x))` of the vertices.  Every
full normal is `c₁ u₁ + c₂ u₂ + c₃ u₃` with `c · q = ±1` on `Q`.  If `Q` met all four antipodal
classes of `{±1}³` (`(1,1,1)`, `(1,1,-1)`, `(1,-1,1)`, `(1,-1,-1)` up to sign), then `c` would be
`±e_i`: only six such `c`.  So eight full normals force `Q` into three classes
(`four_classes_c`).

Classes are encoded by `Fin 4`; `cls3` computes the class of a sign vector.
-/

namespace Kalai5.LemmaB

/-- The four antipodal classes of `{±1}³`, as representatives. -/
def clsRep : Fin 4 → (Fin 3 → ℝ)
  | 0 => ![1, 1, 1]
  | 1 => ![1, 1, -1]
  | 2 => ![1, -1, 1]
  | 3 => ![1, -1, -1]

/-- If `c · q = ±1` for one vector of each of the four classes, then `c = ±e_i`. -/
lemma four_classes_c {c : Fin 3 → ℝ}
    (h0 : c 0 + c 1 + c 2 = 1 ∨ c 0 + c 1 + c 2 = -1)
    (h1 : c 0 + c 1 - c 2 = 1 ∨ c 0 + c 1 - c 2 = -1)
    (h2 : c 0 - c 1 + c 2 = 1 ∨ c 0 - c 1 + c 2 = -1)
    (h3 : c 0 - c 1 - c 2 = 1 ∨ c 0 - c 1 - c 2 = -1) :
    (c 0 = 1 ∨ c 0 = -1) ∧ c 1 = 0 ∧ c 2 = 0 ∨
      c 0 = 0 ∧ (c 1 = 1 ∨ c 1 = -1) ∧ c 2 = 0 ∨
      c 0 = 0 ∧ c 1 = 0 ∧ (c 2 = 1 ∨ c 2 = -1) := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3
  all_goals first
    | (left; refine ⟨Or.inl ?_, ?_, ?_⟩ <;> linarith)
    | (left; refine ⟨Or.inr ?_, ?_, ?_⟩ <;> linarith)
    | (right; left; refine ⟨?_, Or.inl ?_, ?_⟩ <;> linarith)
    | (right; left; refine ⟨?_, Or.inr ?_, ?_⟩ <;> linarith)
    | (right; right; refine ⟨?_, ?_, Or.inl ?_⟩ <;> linarith)
    | (right; right; refine ⟨?_, ?_, Or.inr ?_⟩ <;> linarith)
    | (exfalso; linarith)

/-- The class of a sign vector (normalized to first coordinate `+1`). -/
noncomputable def cls4 (q : Fin 3 → ℝ) : Fin 4 :=
  if q 1 * q 0 = 1 then (if q 2 * q 0 = 1 then 0 else 1) else (if q 2 * q 0 = 1 then 2 else 3)

/-- A sign vector is `±` its class representative. -/
lemma eq_smul_clsRep {q : Fin 3 → ℝ} (h0 : q 0 = 1 ∨ q 0 = -1) (h1 : q 1 = 1 ∨ q 1 = -1)
    (h2 : q 2 = 1 ∨ q 2 = -1) : q = q 0 • clsRep (cls4 q) := by
  funext i
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    fin_cases i <;> simp [cls4, clsRep, h0, h1, h2] <;> norm_num <;> dsimp <;> norm_num

/-- With the fourth class missing, octahedral coordinates are solvable. -/
lemma solve_three (a : Fin 3 → ℝ) : ∃ l : Fin 3 → ℝ, ∀ j : Fin 3,
    l 0 * clsRep (Fin.castSucc j) 0 + l 1 * clsRep (Fin.castSucc j) 1 +
      l 2 * clsRep (Fin.castSucc j) 2 = a j := by
  refine ⟨![(a 1 + a 2) / 2, (a 0 - a 2) / 2, (a 0 - a 1) / 2], fun j => ?_⟩
  fin_cases j <;> simp [clsRep] <;> ring

end Kalai5.LemmaB
