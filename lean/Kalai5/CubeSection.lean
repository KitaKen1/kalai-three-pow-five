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
# Faces of central sections of the cube

A face of the cube `[-1,1]ⁿ` is encoded by `s : Fin n → Tri` (coordinate fixed to `+1`, fixed to
`-1`, or free).  For a weight vector `a ≥ 0` the linear form `⟨a, ·⟩` takes, on the face `s`,
the minimum `2·wt pos - A` and the maximum `A - 2·wt neg`, where `A = Σ aᵢ`.  The relative
interior of the face meets the hyperplane `a^⊥` iff `MeetsSection a s`.

Main result (`three_pow_le_three_mul_sectionFaceCount`): the number of such faces is at least
`3^(n-1)`.  The proof is a *cyclic orbit argument*: under the coordinatewise shift
`pos ↦ neg ↦ free ↦ pos` at most one face of every orbit lies weakly on the positive side of
`a^⊥` without lying in it, so at most `3^(n-1)` faces do; by the antipodal symmetry the same
holds on the negative side, and every remaining face meets the section.

Via polarity, a centrally symmetric `d`-polytope with at most `2d+2` vertices is the polar of a
central section of the `(d+1)`-cube, so this gives the `3^d` bound for such polytopes in every
dimension; for `d = 5` it replaces the 575-strata enumeration of the "at most twelve" theorem.
-/

namespace Kalai5

open Finset

/-- Status of a coordinate in a face of the cube `[-1,1]ⁿ`. -/
inductive Tri
  | pos
  | neg
  | free
  deriving DecidableEq, Repr

namespace Tri

instance : Fintype Tri where
  elems := {pos, neg, free}
  complete x := by cases x <;> simp

/-- The cyclic shift `pos ↦ neg ↦ free ↦ pos`. -/
def rot : Tri → Tri
  | pos => neg
  | neg => free
  | free => pos

/-- Exchange of `pos` and `neg` (the antipodal face). -/
def flip : Tri → Tri
  | pos => neg
  | neg => pos
  | free => free

@[simp] lemma rot_rot_rot (c : Tri) : rot (rot (rot c)) = c := by cases c <;> rfl

@[simp] lemma flip_flip (c : Tri) : flip (flip c) = c := by cases c <;> rfl

@[simp] lemma card : Fintype.card Tri = 3 := by decide

end Tri

variable {n : ℕ}

/-- Total weight of the coordinates on which the face `s` has status `c`. -/
noncomputable def wt (a : Fin n → ℝ) (s : Fin n → Tri) (c : Tri) : ℝ :=
  ∑ i, if s i = c then a i else 0

/-- The face `s` lies weakly on the positive side of `a^⊥` but is not contained in `a^⊥`
(for `a ≥ 0`: minimum `≥ 0` and maximum `> 0`). -/
def PosSide (a : Fin n → ℝ) (s : Fin n → Tri) : Prop :=
  ∑ i, a i ≤ 2 * wt a s .pos ∧ 2 * wt a s .neg < ∑ i, a i

/-- The relative interior of the face `s` meets `a^⊥` (for `a ≥ 0`): either the minimum is `< 0`
and the maximum is `> 0`, or the face lies in the hyperplane. -/
def MeetsSection (a : Fin n → ℝ) (s : Fin n → Tri) : Prop :=
  (2 * wt a s .pos < ∑ i, a i ∧ 2 * wt a s .neg < ∑ i, a i) ∨
    (2 * wt a s .pos = ∑ i, a i ∧ 2 * wt a s .neg = ∑ i, a i)

open Classical in
/-- Number of nonempty faces of the central section `[-1,1]ⁿ ∩ a^⊥`, counted through the faces
of the cube whose relative interior meets the hyperplane. -/
noncomputable def sectionFaceCount (a : Fin n → ℝ) : ℕ :=
  #(univ.filter (fun s : Fin n → Tri => MeetsSection a s))

section weights

variable (a : Fin n → ℝ) (s : Fin n → Tri)

lemma wt_rot_pos : wt a (Tri.rot ∘ s) .pos = wt a s .free := by
  unfold wt; refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [Tri.rot, h]

lemma wt_rot_neg : wt a (Tri.rot ∘ s) .neg = wt a s .pos := by
  unfold wt; refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [Tri.rot, h]

lemma wt_rot_rot_pos : wt a (Tri.rot ∘ Tri.rot ∘ s) .pos = wt a s .neg := by
  unfold wt; refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [Tri.rot, h]

lemma wt_flip_pos : wt a (Tri.flip ∘ s) .pos = wt a s .neg := by
  unfold wt; refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [Tri.flip, h]

lemma wt_flip_neg : wt a (Tri.flip ∘ s) .neg = wt a s .pos := by
  unfold wt; refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [Tri.flip, h]

lemma wt_add : wt a s .pos + wt a s .neg + wt a s .free = ∑ i, a i := by
  unfold wt; rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases h : s i <;> simp [h]

lemma wt_nonneg (ha : ∀ i, 0 ≤ a i) (c : Tri) : 0 ≤ wt a s c := by
  unfold wt; exact sum_nonneg fun i _ => by split_ifs <;> simp [ha i]

end weights

/-- No two faces of one orbit of the cyclic shift both lie on the positive side. -/
lemma not_posSide_rot {a : Fin n → ℝ} {s : Fin n → Tri} (h : PosSide a s) :
    ¬ PosSide a (Tri.rot ∘ s) := by
  rintro ⟨-, h2⟩
  rw [wt_rot_neg] at h2
  exact absurd h.1 (not_le.2 h2)

lemma not_posSide_rot_rot {a : Fin n → ℝ} {s : Fin n → Tri} (h : PosSide a s) :
    ¬ PosSide a (Tri.rot ∘ Tri.rot ∘ s) := by
  rintro ⟨h1, -⟩
  rw [wt_rot_rot_pos] at h1
  exact absurd h.2 (not_lt.2 h1)

/-- The shift `s ↦ rot ∘ s` as an equivalence. -/
def rotEquiv : (Fin n → Tri) ≃ (Fin n → Tri) where
  toFun s := Tri.rot ∘ s
  invFun s := Tri.rot ∘ Tri.rot ∘ s
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

/-- The antipodal map `s ↦ flip ∘ s` as an equivalence. -/
def flipEquiv : (Fin n → Tri) ≃ (Fin n → Tri) where
  toFun s := Tri.flip ∘ s
  invFun s := Tri.flip ∘ s
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

open Classical in
/-- **Cyclic orbit bound.** At most a third of the faces of the cube lie weakly on the positive
side of a hyperplane through the centre without lying in it. (No sign condition on `a`.) -/
theorem three_mul_card_posSide_le (a : Fin n → ℝ) :
    3 * #(univ.filter (PosSide a)) ≤ 3 ^ n := by
  set C := univ.filter (PosSide a)
  set C₁ := univ.filter (fun s => PosSide a (Tri.rot ∘ s))
  set C₂ := univ.filter (fun s => PosSide a (Tri.rot ∘ Tri.rot ∘ s))
  have h₁ : #C₁ = #C := card_equiv rotEquiv (by intro s; simp [C, C₁, rotEquiv])
  have h₂ : #C₂ = #C := card_equiv (rotEquiv.trans rotEquiv)
    (by intro s; simp [C, C₂, rotEquiv])
  have d₁ : Disjoint C C₁ := by
    rw [disjoint_filter]; intro s _ hs; exact not_posSide_rot hs
  have d₂ : Disjoint C C₂ := by
    rw [disjoint_filter]; intro s _ hs; exact not_posSide_rot_rot hs
  have d₁₂ : Disjoint C₁ C₂ := by
    rw [disjoint_filter]; intro s _ hs
    have := not_posSide_rot hs
    simpa [Function.comp_assoc] using this
  have hcard : #(C ∪ C₁ ∪ C₂) = #C + #C₁ + #C₂ := by
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨d₂, d₁₂⟩), card_union_of_disjoint d₁]
  have hle : #(C ∪ C₁ ∪ C₂) ≤ 3 ^ n := by
    simpa using card_le_univ (C ∪ C₁ ∪ C₂)
  omega

section trichotomy

variable {a : Fin n → ℝ}

/-- Every face meets the section, or lies on the positive side, or its antipode does. -/
lemma meets_or_posSide (ha : ∀ i, 0 ≤ a i) (s : Fin n → Tri) :
    MeetsSection a s ∨ PosSide a s ∨ PosSide a (Tri.flip ∘ s) := by
  unfold MeetsSection PosSide
  rw [wt_flip_pos, wt_flip_neg]
  have hsum := wt_add a s
  have hfree := wt_nonneg a s ha .free
  by_cases hp : 2 * wt a s .pos < ∑ i, a i <;> by_cases hm : 2 * wt a s .neg < ∑ i, a i
  · exact Or.inl (Or.inl ⟨hp, hm⟩)
  · exact Or.inr (Or.inr ⟨not_lt.1 hm, hp⟩)
  · exact Or.inr (Or.inl ⟨not_lt.1 hp, hm⟩)
  · refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> linarith [not_lt.1 hp, not_lt.1 hm]

lemma not_posSide_of_meets {s : Fin n → Tri} (h : MeetsSection a s) : ¬ PosSide a s := by
  rintro ⟨h3, h4⟩
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith

lemma not_posSide_flip_of_meets {s : Fin n → Tri} (h : MeetsSection a s) :
    ¬ PosSide a (Tri.flip ∘ s) := by
  rintro ⟨h3, h4⟩
  rw [wt_flip_pos] at h3; rw [wt_flip_neg] at h4
  rcases h with ⟨-, h1⟩ | ⟨h2, -⟩ <;> linarith

lemma not_posSide_flip_of_posSide {s : Fin n → Tri} (h : PosSide a s) :
    ¬ PosSide a (Tri.flip ∘ s) := by
  rintro ⟨-, h4⟩
  rw [wt_flip_neg] at h4
  linarith [h.1]

end trichotomy

open Classical in
/-- **Central sections of the cube have at least `3^(n-1)` faces**, in the form
`3^n ≤ 3 · sectionFaceCount a` (for `a ≥ 0`). -/
theorem three_pow_le_three_mul_sectionFaceCount (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    3 ^ n ≤ 3 * sectionFaceCount a := by
  have hbound := three_mul_card_posSide_le a
  have hflip : #(univ.filter (fun s => PosSide a (Tri.flip ∘ s))) = #(univ.filter (PosSide a)) :=
    card_equiv flipEquiv (by intro s; simp [flipEquiv])
  have dNC : Disjoint (univ.filter (fun s : Fin n → Tri => MeetsSection a s))
      (univ.filter (PosSide a)) :=
    disjoint_filter.2 fun _ _ h => not_posSide_of_meets h
  have dNC' : Disjoint (univ.filter (fun s : Fin n → Tri => MeetsSection a s))
      (univ.filter (fun s => PosSide a (Tri.flip ∘ s))) :=
    disjoint_filter.2 fun _ _ h => not_posSide_flip_of_meets h
  have dCC' : Disjoint (univ.filter (PosSide a))
      (univ.filter (fun s => PosSide a (Tri.flip ∘ s))) :=
    disjoint_filter.2 fun _ _ h => not_posSide_flip_of_posSide h
  have hcover : univ.filter (fun s : Fin n → Tri => MeetsSection a s) ∪ univ.filter (PosSide a)
      ∪ univ.filter (fun s => PosSide a (Tri.flip ∘ s)) = univ := by
    refine eq_univ_of_forall fun s => ?_
    rcases meets_or_posSide ha s with h | h | h <;> simp [h]
  have hcard := congrArg Finset.card hcover
  rw [card_union_of_disjoint (disjoint_union_left.2 ⟨dNC', dCC'⟩),
    card_union_of_disjoint dNC] at hcard
  simp only [card_univ, Fintype.card_pi, Tri.card, prod_const, Fintype.card_fin] at hcard
  unfold sectionFaceCount
  omega

/-- The case used for the "at most twelve vertices" theorem: central sections of the 6-cube
have at least `243 = 3^5` nonempty faces. -/
theorem le_sectionFaceCount_six (a : Fin 6 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    243 ≤ sectionFaceCount a := by
  have := three_pow_le_three_mul_sectionFaceCount a ha
  norm_num at this
  omega

end Kalai5
