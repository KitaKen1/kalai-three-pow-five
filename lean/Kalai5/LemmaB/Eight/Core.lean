import Kalai5.LemmaB.Eight.Types
import Kalai5.LemmaB.Eight.Normal
import Kalai5.LemmaB.Assemble

/-!
# Lemma B at sixteen vertices: the core and the rank-three octahedral case

`coreClaim8`: a rank-three configuration of eight pairs without a fourth `±1`-functional has at
least `243` nonempty faces (classes sorted by size: `(6,1,1)`, `(5,2,1)`, `(4,3,1)`, `(4,2,2)`,
`(3,3,2)`).

`IsCSPolytope5.rank3_oct16`: a centrally symmetric 5-polytope with sixteen vertices whose full
normals contain three independent ones and avoid one of the four classes of `{±1}³` (the
octahedral case, e.g. four full pairs spanning only three dimensions) has four independent full
normals or at least `243` faces.
-/

namespace Kalai5.LemmaB.Eight

open Set Module LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The counting core at sixteen vertices. -/
def CoreClaim8 : Prop := ∀ (x : Fin 8 → E5) (C : Config x), ¬ C.ExtraPM →
  243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard

/-- **Lemma B (core), eight pairs.** -/
theorem coreClaim8 : CoreClaim8 := by
  intro x C hX
  obtain ⟨τ, hτ1, hτ2⟩ := Config.exists_perm_antitone (fun j => (C.cls j).card)
  have hX' : ¬ (C.perm τ.symm).ExtraPM := fun h => hX (C.extraPM_of_perm τ.symm h)
  have hcls : ∀ j, ((C.perm τ.symm).cls j).card = (C.cls (τ j)).card := fun j => by
    rw [C.cls_perm, Equiv.symm_symm]
  have hsum := (C.perm τ.symm).sum_card_cls
  rw [hcls, hcls, hcls] at hsum
  have hp0 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 0)
  have hp1 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 1)
  have hp2 := Finset.card_pos.2 ((C.perm τ.symm).cls_nonempty 2)
  rw [hcls] at hp0 hp1 hp2
  obtain h | h | h | h | h : ((C.cls (τ 0)).card = 6 ∧ (C.cls (τ 1)).card = 1 ∧
        (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 5 ∧ (C.cls (τ 1)).card = 2 ∧ (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 4 ∧ (C.cls (τ 1)).card = 3 ∧ (C.cls (τ 2)).card = 1) ∨
      ((C.cls (τ 0)).card = 4 ∧ (C.cls (τ 1)).card = 2 ∧ (C.cls (τ 2)).card = 2) ∨
      ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 3 ∧ (C.cls (τ 2)).card = 2) := by
    omega
  · exact (C.perm τ.symm).count_611 (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_521 (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_431 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_422 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)
  · exact (C.perm τ.symm).count_332 hX' (by rw [hcls]; exact h.1) (by rw [hcls]; exact h.2.1)
      (by rw [hcls]; exact h.2.2)

variable {P : Set E5}

/-- **Rank three, octahedral, sixteen vertices.**  Three independent full normals whose positions
avoid one class of `{±1}³`: four independent full normals, or at least `243` faces. -/
theorem IsCSPolytope5.rank3_oct16 (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16)
    {u : Fin 3 → E5} (hu : LinearIndependent ℝ u)
    (hpm : ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u i, y⟫ = 1 ∨ ⟪u i, y⟫ = -1) {m : Fin 4}
    (hmiss : ∀ y ∈ P.extremePoints ℝ,
      (fun i => ⟪u i, y⟫) ≠ clsRep m ∧ (fun i => ⟪u i, y⟫) ≠ -clsRep m) :
    (∃ u4 : Fin 4 → E5, LinearIndependent ℝ u4 ∧
      ∀ i, ∀ y ∈ P.extremePoints ℝ, ⟪u4 i, y⟫ = 1 ∨ ⟪u4 i, y⟫ = -1) ∨
      243 ≤ (faces P).ncard := by
  obtain ⟨x, -, hxrange, C, hCE⟩ := IsCSPolytope5.rank3_normal hP h16 hu hpm hmiss
  by_cases hE : C.ExtraPM
  · exact Or.inl (hCE hE)
  · right
    obtain ⟨V, hV⟩ := hP.polytope
    have h := coreClaim8 x C hE
    rwa [hxrange, hV, convexHull_extremePoints_eq, ← hV] at h

end Kalai5.LemmaB.Eight
