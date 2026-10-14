import Kalai5.FullPrism.Core

/-!
# Exposed faces of `conv {±v_j}` from sign patterns

For `z` with `|⟪z, v_j⟫| ≤ 1` for all `j`, the points of `{±v_j}` where `⟪z, ·⟫ = 1` form a face
index (`isFaceIdx_idxOf`).  It only depends on the *sign pattern* of the values (`1`, `-1`, or
neither) at the eight points (`idxOf_eq_patIdx`), and different patterns give different faces
(`patIdx_injOn`).
-/

namespace Kalai5.FullPrism

open Set Module Kalai5.Gale

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {v : Fin 8 → E5}

/-- Face index of `z`: the points where `⟪z, ·⟫ = 1`. -/
noncomputable def idxOf (v : Fin 8 → E5) (z : E5) : Finset (Fin 16) :=
  Finset.univ.filter fun i => ⟪z, pm16 v i⟫ = 1

lemma pm16_lo (v : Fin 8 → E5) (j : Fin 8) : pm16 v ⟨j, by omega⟩ = v j := by
  simp [pm16, j.2]

lemma pm16_hi (v : Fin 8 → E5) (j : Fin 8) : pm16 v ⟨j + 8, by omega⟩ = -v j := by
  simp [pm16]

lemma isFaceIdx_idxOf {z : E5} (hz : ∀ j, |⟪z, v j⟫| ≤ 1) : IsFaceIdx (pm16 v) (idxOf v z) := by
  have hle : ∀ i, ⟪z, pm16 v i⟫ ≤ 1 := by
    intro i
    unfold pm16
    split_ifs with h
    · exact (abs_le.1 (hz _)).2
    · rw [inner_neg_right]; linarith [(abs_le.1 (hz ⟨i.val - 8, by omega⟩)).1]
  refine ⟨evalMap (pm16 v) (-z, 1), evalMap_mem_affVals _ _, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [idxOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [evalMap_apply, inner_neg_left, hi]
  · simp only [idxOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [evalMap_apply, inner_neg_left]
    have := lt_of_le_of_ne (hle i) hi
    linarith

/-- The sign of a value relative to `±1`. -/
noncomputable def sgnOf (x : ℝ) : ℤ := if x = 1 then 1 else if x = -1 then -1 else 0

lemma sgnOf_eq_one {x : ℝ} : sgnOf x = 1 ↔ x = 1 := by
  unfold sgnOf; split_ifs with h1 h2 <;> simp_all

lemma sgnOf_eq_neg_one {x : ℝ} : sgnOf x = -1 ↔ x = -1 := by
  unfold sgnOf; split_ifs with h1 h2 <;> simp_all <;> norm_num

/-- Entry `j` of a pattern given by pairs. -/
def sel (s : Fin 4 → ℤ × ℤ) (j : ℕ) : ℤ := if j % 2 = 0 then (s ⟨j / 2 % 4, by omega⟩).1
  else (s ⟨j / 2 % 4, by omega⟩).2

/-- Face index of a sign pattern. -/
def patIdx (s : Fin 4 → ℤ × ℤ) : Finset (Fin 16) :=
  Finset.univ.filter fun i => if i.val < 8 then sel s i = 1 else sel s (i - 8) = -1

lemma vp_eq (v : Fin 8 → E5) (k : Fin 4) : vp v k = v ⟨2 * k, by omega⟩ := rfl
lemma vm_eq (v : Fin 8 → E5) (k : Fin 4) : vm v k = v ⟨2 * k + 1, by omega⟩ := rfl

/-- The value of `z` at point `j` in terms of the pairs. -/
lemma inner_v_eq {z : E5} {ξp ξm : Fin 4 → ℝ} (hz : ∀ k, ⟪z, vp v k⟫ = ξp k ∧ ⟪z, vm v k⟫ = ξm k)
    (j : Fin 8) : ⟪z, v j⟫ = if j.val % 2 = 0 then ξp ⟨j / 2 % 4, by omega⟩
      else ξm ⟨j / 2 % 4, by omega⟩ := by
  split_ifs with h
  · have := (hz ⟨j / 2 % 4, by omega⟩).1
    rw [vp_eq] at this
    convert this using 3
    ext; simp only; omega
  · have := (hz ⟨j / 2 % 4, by omega⟩).2
    rw [vm_eq] at this
    convert this using 3
    ext; simp only; omega

/-- **The face index depends only on the sign pattern.** -/
lemma idxOf_eq_patIdx {z : E5} {ξp ξm : Fin 4 → ℝ}
    (hz : ∀ k, ⟪z, vp v k⟫ = ξp k ∧ ⟪z, vm v k⟫ = ξm k) :
    idxOf v z = patIdx (fun k => (sgnOf (ξp k), sgnOf (ξm k))) := by
  ext i
  simp only [idxOf, patIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < 8
  · rw [if_pos hi]
    have hpm : pm16 v i = v ⟨i, hi⟩ := by simp [pm16, hi]
    rw [hpm, inner_v_eq hz]
    simp only [sel]
    split_ifs <;> simp [sgnOf_eq_one]
  · rw [if_neg hi]
    have hpm : pm16 v i = -v ⟨i - 8, by omega⟩ := by simp [pm16, hi]
    rw [hpm, inner_neg_right, inner_v_eq hz]
    simp only [sel]
    have h8 : (i.val - 8) % 2 = 0 ↔ (⟨i.val - 8, by omega⟩ : Fin 8).val % 2 = 0 := Iff.rfl
    split_ifs with h1 h2 h2 <;> simp_all [sgnOf_eq_neg_one, neg_eq_iff_eq_neg]

/-- Patterns with entries in `{-1, 0, 1}`. -/
def IsPat (s : Fin 4 → ℤ × ℤ) : Prop :=
  ∀ k, ((s k).1 = -1 ∨ (s k).1 = 0 ∨ (s k).1 = 1) ∧ ((s k).2 = -1 ∨ (s k).2 = 0 ∨ (s k).2 = 1)

lemma isPat_sgnOf (ξp ξm : Fin 4 → ℝ) : IsPat fun k => (sgnOf (ξp k), sgnOf (ξm k)) := by
  intro k
  simp only [sgnOf]
  constructor <;> split_ifs <;> simp

lemma mem_patIdx_p (s : Fin 4 → ℤ × ℤ) (k : Fin 4) :
    (⟨2 * k, by omega⟩ : Fin 16) ∈ patIdx s ↔ (s k).1 = 1 := by
  simp only [patIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [if_pos (show 2 * (k : ℕ) < 8 by omega)]
  unfold sel
  rw [if_pos (show 2 * (k : ℕ) % 2 = 0 by omega)]
  have : (⟨2 * (k : ℕ) / 2 % 4, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  rw [this]

lemma mem_patIdx_m (s : Fin 4 → ℤ × ℤ) (k : Fin 4) :
    (⟨2 * k + 1, by omega⟩ : Fin 16) ∈ patIdx s ↔ (s k).2 = 1 := by
  simp only [patIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [if_pos (show 2 * (k : ℕ) + 1 < 8 by omega)]
  unfold sel
  rw [if_neg (show ¬ ((2 * (k : ℕ) + 1) % 2 = 0) by omega)]
  have : (⟨(2 * (k : ℕ) + 1) / 2 % 4, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  rw [this]

lemma mem_patIdx_p' (s : Fin 4 → ℤ × ℤ) (k : Fin 4) :
    (⟨2 * k + 8, by omega⟩ : Fin 16) ∈ patIdx s ↔ (s k).1 = -1 := by
  simp only [patIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [if_neg (show ¬ (2 * (k : ℕ) + 8 < 8) by omega)]
  unfold sel
  rw [if_pos (show (2 * (k : ℕ) + 8 - 8) % 2 = 0 by omega)]
  have : (⟨(2 * (k : ℕ) + 8 - 8) / 2 % 4, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  rw [this]

lemma mem_patIdx_m' (s : Fin 4 → ℤ × ℤ) (k : Fin 4) :
    (⟨2 * k + 9, by omega⟩ : Fin 16) ∈ patIdx s ↔ (s k).2 = -1 := by
  simp only [patIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [if_neg (show ¬ (2 * (k : ℕ) + 9 < 8) by omega)]
  unfold sel
  rw [if_neg (show ¬ ((2 * (k : ℕ) + 9 - 8) % 2 = 0) by omega)]
  have : (⟨(2 * (k : ℕ) + 9 - 8) / 2 % 4, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  rw [this]

lemma pat_val {a : ℤ} (ha : a = -1 ∨ a = 0 ∨ a = 1) {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (h1 : a = 1 ↔ b = 1) (h2 : a = -1 ↔ b = -1) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

/-- **Different patterns give different faces.** -/
lemma patIdx_injOn {s s' : Fin 4 → ℤ × ℤ} (hs : IsPat s) (hs' : IsPat s')
    (h : patIdx s = patIdx s') : s = s' := by
  funext k
  refine Prod.ext (pat_val (hs k).1 (hs' k).1 ?_ ?_) (pat_val (hs k).2 (hs' k).2 ?_ ?_)
  · rw [← mem_patIdx_p, ← mem_patIdx_p, h]
  · rw [← mem_patIdx_p', ← mem_patIdx_p', h]
  · rw [← mem_patIdx_m, ← mem_patIdx_m, h]
  · rw [← mem_patIdx_m', ← mem_patIdx_m', h]

lemma patIdx_ne_univ (s : Fin 4 → ℤ × ℤ) : patIdx s ≠ Finset.univ := by
  intro h
  have h1 := (mem_patIdx_p s 0).1 (by rw [h]; exact Finset.mem_univ _)
  have h2 := (mem_patIdx_p' s 0).1 (by rw [h]; exact Finset.mem_univ _)
  rw [h1] at h2
  norm_num at h2

lemma patIdx_nonempty {s : Fin 4 → ℤ × ℤ} {k : Fin 4} (h : s k ≠ (0, 0)) (hs : IsPat s) :
    (patIdx s).Nonempty := by
  rcases hs k with ⟨h1 | h1 | h1, h2 | h2 | h2⟩
  · exact ⟨_, (mem_patIdx_p' s k).2 h1⟩
  · exact ⟨_, (mem_patIdx_p' s k).2 h1⟩
  · exact ⟨_, (mem_patIdx_p' s k).2 h1⟩
  · exact ⟨_, (mem_patIdx_m' s k).2 h2⟩
  · exact absurd (Prod.ext h1 h2) h
  · exact ⟨_, (mem_patIdx_m s k).2 h2⟩
  · exact ⟨_, (mem_patIdx_p s k).2 h1⟩
  · exact ⟨_, (mem_patIdx_p s k).2 h1⟩
  · exact ⟨_, (mem_patIdx_p s k).2 h1⟩

end Kalai5.FullPrism
