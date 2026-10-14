import Kalai5.Cube3.TriangleCount
import Kalai5.Cube3.NoSegments

/-! At most eighteen facets force a shared edge direction in the (3,3,1,1) distribution. -/

namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} (C : Config x)

def Config.SharedEdgeDirection (j k : Fin 4) : Prop :=
  ∃ n,LemmaB.IsEdgeNormal (fibre C.c C.k j) n ∧
    (LemmaB.IsEdgeNormal (fibre C.c C.k k) n ∨ LemmaB.IsEdgeNormal (fibre C.c C.k k) (-n))

lemma balanceSign_parallel (j k : Fin 4) {n m : E 2} (h : n=m ∨ n= -m) :
    balanceSign j • n=balanceSign k • m ∨ balanceSign j • n= -(balanceSign k • m) := by
  rcases balanceSign_sign j with hj | hj <;>
    rcases balanceSign_sign k with hk | hk <;> rcases h with h | h <;> simp [hj,hk,h]

variable {C}

lemma TriangleFibre.shared_of_parallel {j k : Fin 4} (T : TriangleFibre C j) (U : TriangleFibre C k)
    {a b : Fin 3} (h : T.triangle.normal a=U.triangle.normal b ∨
      T.triangle.normal a= -U.triangle.normal b) : C.SharedEdgeDirection j k := by
  refine ⟨balanceSign j • T.triangle.normal a,T.unsigned_normal a,?_⟩
  rcases balanceSign_parallel j k h with he | he
  · exact Or.inl (he.symm ▸ U.unsigned_normal b)
  · apply Or.inr
    rw [he,neg_neg]
    exact U.unsigned_normal b

theorem Config.disjoint_triangles_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=3) (h1 : (C.cls (τ 1)).card=3)
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (hno : ¬ C.SharedEdgeDirection (τ 0) (τ 1)) : 22 ≤ fvec P 4 := by
  obtain ⟨T⟩ := C.triangle_fibre h0
  obtain ⟨U⟩ := C.triangle_fibre h1
  exact T.two_triangles_facets hP hrange τ U h2 h3
    (fun _ _ h => hno (T.shared_of_parallel U (Or.inl h)))
    (fun _ _ h => hno (T.shared_of_parallel U (Or.inr h)))

theorem Config.shared_triangle_edge {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=3) (h1 : (C.cls (τ 1)).card=3)
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.SharedEdgeDirection (τ 0) (τ 1) := by
  by_contra hno
  have h22 := C.disjoint_triangles_facets hP hrange τ h0 h1 h2 h3 hno
  omega

/-- The complete size-pattern reduction, with the geometric restriction on two triangles. -/
theorem Config.three_patterns_shared {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=3 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 ∧ C.SharedEdgeDirection (τ 0) (τ 1)) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=2 ∧ (C.cls (τ 3)).card=1) := by
  obtain ⟨τ,h | h | h⟩ := C.three_size_patterns hP hrange hh hno
  · exact ⟨τ,Or.inl h⟩
  · exact ⟨τ,Or.inr (Or.inl ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,
      C.shared_triangle_edge hP hrange hh τ h.1 h.2.1 h.2.2.1 h.2.2.2⟩)⟩
  · exact ⟨τ,Or.inr (Or.inr h)⟩

end Kalai5.Cube3
