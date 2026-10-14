import Kalai5.LemmaA.ReduceSound
import Kalai5.FullPrism.Pattern

/-!
# Lemma B: exposed faces of `conv {±y_v}` from sign patterns (seven pairs)

For `z` with `|⟪z, y_v⟫| ≤ 1` for all `v`, the points of `{±y_v}` where `⟪z, ·⟫ = 1` form a face
index; it depends only on the sign pattern `s v ∈ {1, -1, 0}` (value `1`, `-1`, or neither), and
different patterns give different faces.  `card_add_one_le7`: realizable nonzero patterns give
that many faces, plus `P` itself.
-/

namespace Kalai5.LemmaB

open Set Module Kalai5.Gale Kalai5.LemmaA Kalai5.FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {y : Fin 7 → E5}

/-- Face index of `z`. -/
noncomputable def idx7 (y : Fin 7 → E5) (z : E5) : Finset (Fin 14) :=
  Finset.univ.filter fun i => ⟪z, pm y i⟫ = 1

lemma isFaceIdx_idx7 {z : E5} (hz : ∀ v, |⟪z, y v⟫| ≤ 1) : IsFaceIdx (pm y) (idx7 y z) := by
  have hle : ∀ i, ⟪z, pm y i⟫ ≤ 1 := by
    intro i
    unfold pm
    split_ifs with h
    · exact (abs_le.1 (hz _)).2
    · rw [inner_neg_right]; linarith [(abs_le.1 (hz ⟨i.val - 7, by omega⟩)).1]
  refine ⟨evalMap (pm y) (-z, 1), evalMap_mem_affVals _ _, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [idx7, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [evalMap_apply, inner_neg_left, hi]
  · simp only [idx7, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [evalMap_apply, inner_neg_left]
    have := lt_of_le_of_ne (hle i) hi
    linarith

/-- Face index of a sign pattern. -/
def pat7 (s : Fin 7 → ℤ) : Finset (Fin 14) :=
  Finset.univ.filter fun i => if h : i.val < 7 then s ⟨i, h⟩ = 1 else s ⟨i.val - 7, by omega⟩ = -1

lemma mem_pat7_lo (s : Fin 7 → ℤ) (v : Fin 7) : (⟨v, by omega⟩ : Fin 14) ∈ pat7 s ↔ s v = 1 := by
  simp [pat7, v.2]

lemma mem_pat7_hi (s : Fin 7 → ℤ) (v : Fin 7) :
    (⟨v + 7, by omega⟩ : Fin 14) ∈ pat7 s ↔ s v = -1 := by
  simp [pat7]

/-- **The face index depends only on the sign pattern.** -/
lemma idx7_eq_pat7 {z : E5} {ξ : Fin 7 → ℝ} (hz : ∀ v, ⟪z, y v⟫ = ξ v) :
    idx7 y z = pat7 (fun v => sgnOf (ξ v)) := by
  ext i
  simp only [idx7, pat7, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < 7
  · rw [dif_pos hi]
    have : pm y i = y ⟨i, hi⟩ := by simp [pm, hi]
    rw [this, hz, sgnOf_eq_one]
  · rw [dif_neg hi]
    have : pm y i = -y ⟨i.val - 7, by omega⟩ := by simp [pm, hi]
    rw [this, inner_neg_right, hz, sgnOf_eq_neg_one, neg_eq_iff_eq_neg]

/-- Patterns with values in `{-1, 0, 1}`. -/
def IsPat7 (s : Fin 7 → ℤ) : Prop := ∀ v, s v = -1 ∨ s v = 0 ∨ s v = 1

lemma isPat7_sgnOf (ξ : Fin 7 → ℝ) : IsPat7 fun v => sgnOf (ξ v) := by
  intro v
  simp only [sgnOf]
  split_ifs <;> simp

lemma pat7_injOn {s s' : Fin 7 → ℤ} (hs : IsPat7 s) (hs' : IsPat7 s') (h : pat7 s = pat7 s') :
    s = s' := by
  funext v
  refine pat_val (hs v) (hs' v) ?_ ?_
  · rw [← mem_pat7_lo, ← mem_pat7_lo, h]
  · rw [← mem_pat7_hi, ← mem_pat7_hi, h]

lemma pat7_ne_univ (s : Fin 7 → ℤ) : pat7 s ≠ Finset.univ := by
  intro h
  have h1 := (mem_pat7_lo s 0).1 (by rw [h]; exact Finset.mem_univ _)
  have h2 := (mem_pat7_hi s 0).1 (by rw [h]; exact Finset.mem_univ _)
  rw [h1] at h2
  norm_num at h2

lemma pat7_nonempty {s : Fin 7 → ℤ} {v : Fin 7} (h : s v ≠ 0) (hs : IsPat7 s) :
    (pat7 s).Nonempty := by
  rcases hs v with h1 | h1 | h1
  · exact ⟨_, (mem_pat7_hi s v).2 h1⟩
  · exact absurd h1 h
  · exact ⟨_, (mem_pat7_lo s v).2 h1⟩

/-- A pattern realized by a linear form with all values in `[-1, 1]`. -/
def Realizable7 (y : Fin 7 → E5) (s : Fin 7 → ℤ) : Prop :=
  ∃ z : E5, ∃ ξ : Fin 7 → ℝ, (∀ v, ⟪z, y v⟫ = ξ v) ∧ (∀ v, |ξ v| ≤ 1) ∧
    s = fun v => sgnOf (ξ v)

/-- **Each realizable nonzero pattern is a face**, and `P` itself is one more. -/
theorem card_add_one_le7 (T : Finset (Fin 7 → ℤ)) (hT : ∀ s ∈ T, s ≠ 0 ∧ Realizable7 y s) :
    T.card + 1 ≤ (faces (convexHull ℝ (range (pm y)))).ncard := by
  classical
  have hpat : ∀ s ∈ T, IsPat7 s := by
    intro s hs
    obtain ⟨-, z, ξ, -, -, rfl⟩ := hT s hs
    exact isPat7_sgnOf ξ
  have hnot : Finset.univ ∉ T.image pat7 := by
    intro h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    exact pat7_ne_univ s hs
  have hcard : (insert Finset.univ (T.image pat7)).card = T.card + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn]
    intro s hs s' hs' h
    exact pat7_injOn (hpat s hs) (hpat s' hs') h
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
        push_neg at h
        exact hs0 (funext fun v => h v)
      exact pat7_nonempty hv (isPat7_sgnOf ξ)
    · rw [← idx7_eq_pat7 hz]
      apply isFaceIdx_idx7
      intro v
      rw [hz]
      exact hb v

end Kalai5.LemmaB
