import Kalai5.Cube3.Relabel
import Kalai5.Cube3.SingletonCount

/-! The (5,1,1,1) distribution is excluded for every class labeling. -/

namespace Kalai5.Cube3.Config

open Set FullPrism

variable {x : Fin 8 → E5} (C : Config x)

theorem singleton_any_class_impossible {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (j : Fin 4) (h5 : 5 ≤ (C.cls j).card)
    (hsmall : ∀ k, k ≠ j → (C.cls k).card = 1) : False := by
  let R := C.relabel (classPerm j) (classPerm_balanced j)
  apply R.singleton_class_zero_impossible hP hrange hh
  · simpa only [R,relabel_cls,classPerm_zero] using h5
  · intro i
    rw [show R.cls (![1,2,3] i) = C.cls (classPerm j (![1,2,3] i)) from
      C.relabel_cls _ _ _]
    apply hsmall
    intro he
    have he' : (![1,2,3] i : Fin 4) = 0 := (classPerm j).injective
      (he.trans (classPerm_zero j).symm)
    have hval := congrArg Fin.val he'
    fin_cases i <;> norm_num at hval <;> dsimp at hval <;> norm_num at hval

/-- With eight nonempty fibres, a class of size at least five forces all
other classes to be singletons; the polar construction excludes it. -/
theorem fibre_card_le_four {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (j : Fin 4) : (C.cls j).card ≤ 4 := by
  by_contra hbad
  have h5 : 5 ≤ (C.cls j).card := by omega
  apply C.singleton_any_class_impossible hP hrange hh j h5
  have hsum := C.sum_card_cls
  rw [Fin.sum_univ_four] at hsum
  have h0 := Finset.card_pos.2 (C.cls_nonempty 0)
  have h1 := Finset.card_pos.2 (C.cls_nonempty 1)
  have h2 := Finset.card_pos.2 (C.cls_nonempty 2)
  have h3 := Finset.card_pos.2 (C.cls_nonempty 3)
  intro k hkj
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> decide
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> decide
  rcases hj with rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl <;> omega

theorem four_size_patterns {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card = 4 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 1 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 3 ∧
      (C.cls (τ 2)).card = 1 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 2 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 2 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 2 ∧ (C.cls (τ 3)).card = 2) := by
  obtain ⟨τ,hfirst | hrest⟩ := C.five_size_patterns
  · have h := C.fibre_card_le_four hP hrange hh (τ 0)
    omega
  · exact ⟨τ,hrest⟩

end Kalai5.Cube3.Config
