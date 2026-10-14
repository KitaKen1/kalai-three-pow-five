import Kalai5.LemmaB.Pattern

/-!
# Lemma B at sixteen vertices: exposed faces of `conv {±y_v}` from sign patterns (eight pairs)

The eight-point version of `Kalai5.LemmaB.Pattern`, on top of `FullPrism.idxOf`: for `z` with
`|⟪z, y_v⟫| ≤ 1` the face index only depends on the sign pattern `s v ∈ {1, -1, 0}`, different
patterns give different faces, and `card_add_one_le8` counts realizable nonzero patterns, plus `P`.
-/

namespace Kalai5.LemmaB.Eight

open Set Module Kalai5.Gale Kalai5.LemmaA Kalai5.FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {y : Fin 8 → E5}

/-- Face index of a sign pattern. -/
def pat8 (s : Fin 8 → ℤ) : Finset (Fin 16) :=
  Finset.univ.filter fun i => if h : i.val < 8 then s ⟨i, h⟩ = 1 else s ⟨i.val - 8, by omega⟩ = -1

lemma mem_pat8_lo (s : Fin 8 → ℤ) (v : Fin 8) : (⟨v, by omega⟩ : Fin 16) ∈ pat8 s ↔ s v = 1 := by
  simp [pat8, v.2]

lemma mem_pat8_hi (s : Fin 8 → ℤ) (v : Fin 8) :
    (⟨v + 8, by omega⟩ : Fin 16) ∈ pat8 s ↔ s v = -1 := by
  simp [pat8]

/-- **The face index depends only on the sign pattern.** -/
lemma idxOf_eq_pat8 {z : E5} {ξ : Fin 8 → ℝ} (hz : ∀ v, ⟪z, y v⟫ = ξ v) :
    idxOf y z = pat8 (fun v => sgnOf (ξ v)) := by
  ext i
  simp only [idxOf, pat8, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < 8
  · rw [dif_pos hi]
    have : pm16 y i = y ⟨i, hi⟩ := by simp [pm16, hi]
    rw [this, hz, sgnOf_eq_one]
  · rw [dif_neg hi]
    have : pm16 y i = -y ⟨i.val - 8, by omega⟩ := by simp [pm16, hi]
    rw [this, inner_neg_right, hz, sgnOf_eq_neg_one, neg_eq_iff_eq_neg]

/-- Patterns with values in `{-1, 0, 1}`. -/
def IsPat8 (s : Fin 8 → ℤ) : Prop := ∀ v, s v = -1 ∨ s v = 0 ∨ s v = 1

lemma isPat8_sgnOf (ξ : Fin 8 → ℝ) : IsPat8 fun v => sgnOf (ξ v) := by
  intro v
  simp only [sgnOf]
  split_ifs <;> simp

lemma pat8_injOn {s s' : Fin 8 → ℤ} (hs : IsPat8 s) (hs' : IsPat8 s') (h : pat8 s = pat8 s') :
    s = s' := by
  funext v
  refine pat_val (hs v) (hs' v) ?_ ?_
  · rw [← mem_pat8_lo, ← mem_pat8_lo, h]
  · rw [← mem_pat8_hi, ← mem_pat8_hi, h]

lemma pat8_ne_univ (s : Fin 8 → ℤ) : pat8 s ≠ Finset.univ := by
  intro h
  have h1 := (mem_pat8_lo s 0).1 (by rw [h]; exact Finset.mem_univ _)
  have h2 := (mem_pat8_hi s 0).1 (by rw [h]; exact Finset.mem_univ _)
  rw [h1] at h2
  norm_num at h2

lemma pat8_nonempty {s : Fin 8 → ℤ} {v : Fin 8} (h : s v ≠ 0) (hs : IsPat8 s) :
    (pat8 s).Nonempty := by
  rcases hs v with h1 | h1 | h1
  · exact ⟨_, (mem_pat8_hi s v).2 h1⟩
  · exact absurd h1 h
  · exact ⟨_, (mem_pat8_lo s v).2 h1⟩

/-- A pattern realized by a linear form with all values in `[-1, 1]`. -/
def Realizable8 (y : Fin 8 → E5) (s : Fin 8 → ℤ) : Prop :=
  ∃ z : E5, ∃ ξ : Fin 8 → ℝ, (∀ v, ⟪z, y v⟫ = ξ v) ∧ (∀ v, |ξ v| ≤ 1) ∧
    s = fun v => sgnOf (ξ v)

/-- **Each realizable nonzero pattern is a face**, and `P` itself is one more. -/
theorem card_add_one_le8 (T : Finset (Fin 8 → ℤ)) (hT : ∀ s ∈ T, s ≠ 0 ∧ Realizable8 y s) :
    T.card + 1 ≤ (faces (convexHull ℝ (range (pm16 y)))).ncard := by
  classical
  have hpat : ∀ s ∈ T, IsPat8 s := by
    intro s hs
    obtain ⟨-, z, ξ, -, -, rfl⟩ := hT s hs
    exact isPat8_sgnOf ξ
  have hnot : Finset.univ ∉ T.image pat8 := by
    intro h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    exact pat8_ne_univ s hs
  have hcard : (insert Finset.univ (T.image pat8)).card = T.card + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn]
    intro s hs s' hs' h
    exact pat8_injOn (hpat s hs) (hpat s' hs') h
  rw [← hcard]
  apply le_ncard_faces
  intro F hF
  rcases Finset.mem_insert.1 hF with rfl | hF
  · exact ⟨Finset.univ_nonempty, isFaceIdx_univ⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨hs0, z, ξ, hz, hb, rfl⟩ := hT s hs
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv⟩ : ∃ v, sgnOf (ξ v) ≠ 0 := by
        by_contra h
        push Not at h
        exact hs0 (funext fun v => h v)
      exact pat8_nonempty hv (isPat8_sgnOf ξ)
    · rw [← idxOf_eq_pat8 hz]
      apply isFaceIdx_idxOf
      intro v
      rw [hz]
      exact hb v

end Kalai5.LemmaB.Eight
