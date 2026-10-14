import Kalai5.Endpoints.Z20.QuadCore

/-!
# The facets `Y` and `E` through their profiles

* `IsCSPolytope5.Y_quad`: a facet with row `Y = (7,15,14,6; 29)` (profile `[2,3,0,1,0,0,0]`) has
  `q4 = exc = 3`, and each of its quadrilaterals lies in exactly one of its 3-faces with five
  vertices (the other one is the prism).
* `IsCSPolytope5.E_quad`: a facet with row `E = (7,16,16,7; 32)` has `exc = 2`, and each of its
  quadrilaterals lies in exactly one of its 3-faces with five vertices: for the profile
  `[4,2,0,0,1,0,0]` as for `Y`, for `[5,0,0,0,2,0,0]` because there is no quadrilateral.
-/

namespace Kalai5

open Set

open scoped Classical

lemma not_of_filter_card_zero {α : Type*} {s : Finset α} {p : α → Prop} [DecidablePred p]
    (h : (s.filter p).card = 0) {x : α} (hx : x ∈ s) : ¬ p x :=
  Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) hx

lemma eq_of_filter_eq_singleton {α : Type*} {s : Finset α} {p : α → Prop} [DecidablePred p]
    {y : α} (h : s.filter p = {y}) {x : α} (hx : x ∈ s) (hp : p x) : x = y := by
  have : x ∈ s.filter p := Finset.mem_filter.2 ⟨hx, hp⟩
  rw [h] at this
  exact Finset.mem_singleton.1 this

lemma mem_of_filter_eq_singleton {α : Type*} {s : Finset α} {p : α → Prop} [DecidablePred p]
    {y : α} (h : s.filter p = {y}) : y ∈ s ∧ p y := by
  have : y ∈ s.filter p := by rw [h]; exact Finset.mem_singleton_self y
  exact Finset.mem_filter.1 this

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The seven counts of a facet profile. -/
lemma IsCSPolytope5.profile_counts {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) {a b c d e f g : ℕ} (hL : (rowXOf F).2.1 = [a, b, c, d, e, f, g]) :
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (4, 6, 4)).card = a ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 8, 5)).card = b ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 9, 6)).card = c ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 9, 5)).card = d ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 10, 6)).card = e ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 11, 7)).card = f ∧
    ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 12, 8)).card = g := by
  have h := (hP.facet_profile hF h4 hn).2
  rw [hL] at h
  simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm⟩

/-- Every 3-face of a facet with at most seven vertices has one of the seven face numbers. -/
lemma IsCSPolytope5.tri3_cases {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) {T : Set E5} (hT : T ∈ (hP.below_finite F 3).toFinset) :
    tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (5, 9, 6) ∨ tri3 P T = (6, 9, 5) ∨
      tri3 P T = (6, 10, 6) ∨ tri3 P T = (6, 11, 7) ∨ tri3 P T = (6, 12, 8) := by
  have h := (hP.facet_profile hF h4 hn).1 T hT
  simpa [fv7] using h

/-- **Facets `Y`.** -/
theorem IsCSPolytope5.Y_quad {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = excRow) :
    (q4 P F : ℤ) = 3 ∧ exc P F = 3 ∧ ∀ Q, Q ∈ faces P → Q ⊆ F → dim Q = 2 → cnt P Q 0 = 4 →
      ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card = 1 := by
  classical
  have hn : cnt P F 0 = 7 := by
    have := congrArg Row.n hrow
    simpa [faceRow, excRow] using this
  obtain ⟨hmemX, hrowF⟩ := hP.facet_rowX hF h4 hn.le
  have hL := smallRowsX_exc _ hmemX (by
    show rowOf F = excRow
    rw [hrowF, hrow])
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hP.profile_counts hF h4 hn.le hL
  obtain ⟨T6, hT6s⟩ := Finset.card_eq_one.1 c4
  obtain ⟨hT6, hT6t⟩ := mem_of_filter_eq_singleton hT6s
  have hT6' := hT6
  rw [Set.Finite.mem_toFinset] at hT6'
  simp only [tri3, Prod.mk.injEq] at hT6t
  have hexcF : exc P F = 3 := by
    have h := hP.two_exc_profile hF h4 hn.le
    simp only [fv7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    rw [c1, c2, c3, c4, c5, c6, c7] at h
    norm_num at h
    omega
  have hrest : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ T6 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) := by
    intro T hT hne
    rcases hP.tri3_cases hF h4 hn.le hT with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (not_of_filter_card_zero c3 hT)
    · exact absurd (eq_of_filter_eq_singleton hT6s hT h) hne
    · exact absurd h (not_of_filter_card_zero c5 hT)
    · exact absurd h (not_of_filter_card_zero c6 hT)
    · exact absurd h (not_of_filter_card_zero c7 hT)
  have hx6 : exc P T6 ≤ 3 := by
    rw [hP.exc_threeface hT6'.1 hT6'.2.2, hT6t.2.1, hT6t.2.2]
    norm_num
  have hb : ((((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 8, 5)).card : ℕ) :
      ℤ) = exc P F := by
    rw [c2, hexcF]
    norm_num
  obtain ⟨hq, hone⟩ := hP.five_one_core hF h4 hT6 hT6t.1 hx6 hrest hb
  exact ⟨by rw [hq, hexcF], hexcF, hone⟩

/-- **Facets `E`.** -/
theorem IsCSPolytope5.E_quad {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = eRow) :
    exc P F = 2 ∧ ∀ Q, Q ∈ faces P → Q ⊆ F → dim Q = 2 → cnt P Q 0 = 4 →
      ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card = 1 := by
  classical
  have hn : cnt P F 0 = 7 := by
    have := congrArg Row.n hrow
    simpa [faceRow, eRow] using this
  obtain ⟨hmemX, hrowF⟩ := hP.facet_rowX hF h4 hn.le
  rcases smallRowsX_eRow _ hmemX (by
    show rowOf F = eRow
    rw [hrowF, hrow]) with hL | hL
  · -- profile `[4,2,0,0,1,0,0]`
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hP.profile_counts hF h4 hn.le hL
    obtain ⟨T6, hT6s⟩ := Finset.card_eq_one.1 c5
    obtain ⟨hT6, hT6t⟩ := mem_of_filter_eq_singleton hT6s
    have hT6' := hT6
    rw [Set.Finite.mem_toFinset] at hT6'
    simp only [tri3, Prod.mk.injEq] at hT6t
    have hexcF : exc P F = 2 := by
      have h := hP.two_exc_profile hF h4 hn.le
      simp only [fv7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
      rw [c1, c2, c3, c4, c5, c6, c7] at h
      norm_num at h
      omega
    have hrest : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ T6 →
        tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) := by
      intro T hT hne
      rcases hP.tri3_cases hF h4 hn.le hT with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (not_of_filter_card_zero c3 hT)
      · exact absurd h (not_of_filter_card_zero c4 hT)
      · exact absurd (eq_of_filter_eq_singleton hT6s hT h) hne
      · exact absurd h (not_of_filter_card_zero c6 hT)
      · exact absurd h (not_of_filter_card_zero c7 hT)
    have hx6 : exc P T6 ≤ 3 := by
      rw [hP.exc_threeface hT6'.1 hT6'.2.2, hT6t.2.1, hT6t.2.2]
      norm_num
    have hb : ((((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 8, 5)).card : ℕ) :
        ℤ) = exc P F := by
      rw [c2, hexcF]
      norm_num
    exact ⟨hexcF, (hP.five_one_core hF h4 hT6 hT6t.1 hx6 hrest hb).2⟩
  · -- profile `[5,0,0,0,2,0,0]`: no quadrilateral
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hP.profile_counts hF h4 hn.le hL
    obtain ⟨Ta, Tb, hab, hTs⟩ := Finset.card_eq_two.1 c5
    have hTa : Ta ∈ (hP.below_finite F 3).toFinset := by
      have : Ta ∈ (hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 10, 6) := by
        rw [hTs]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_filter.1 this).1
    have hTb : Tb ∈ (hP.below_finite F 3).toFinset := by
      have : Tb ∈ (hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 10, 6) := by
        rw [hTs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.mem_filter.1 this).1
    have hexcF : exc P F = 2 := by
      have h := hP.two_exc_profile hF h4 hn.le
      simp only [fv7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
      rw [c1, c2, c3, c4, c5, c6, c7] at h
      norm_num at h
      omega
    have hrest : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ Ta → T ≠ Tb →
        tri3 P T = (4, 6, 4) := by
      intro T hT hna hnb
      rcases hP.tri3_cases hF h4 hn.le hT with h | h | h | h | h | h | h
      · exact h
      · exact absurd h (not_of_filter_card_zero c2 hT)
      · exact absurd h (not_of_filter_card_zero c3 hT)
      · exact absurd h (not_of_filter_card_zero c4 hT)
      · have : T ∈ (hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (6, 10, 6) :=
          Finset.mem_filter.2 ⟨hT, h⟩
        rw [hTs] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h'
        · exact absurd h' hna
        · exact absurd h' hnb
      · exact absurd h (not_of_filter_card_zero c6 hT)
      · exact absurd h (not_of_filter_card_zero c7 hT)
    have hq0 := hP.q4_zero_core hF h4 hTa hTb hab hrest hexcF
    refine ⟨hexcF, fun Q hQ hQF h2 h4Q => ?_⟩
    have := hP.q4_pos_of_quad hQ hQF h2 h4Q
    omega

end cs

end Kalai5
