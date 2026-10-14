import Kalai5.FullPrism.Count

/-!
# The full prism configuration has at least 243 faces

`prism_core`: eight points `v^±_k` with `u = 1` on all of them and side-facet forms `r_k`
(vanishing on `v^±_j`, `j ≠ k`, positive at `v^±_k`) span a polytope `conv {±v^±_k}` with at least
243 nonempty faces.  Choose the sign of the common direction `w` so that `κ = u(w) ≥ 0`, and orient
each pair so that its coefficient in `w` is positive; then apply `faces_parallel` (`κ = 0`) or
`faces_concurrent` (`κ > 0`).
-/

namespace Kalai5.FullPrism

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma mem_range_pm16 {v : Fin 8 → E5} {x : E5} :
    x ∈ range (pm16 v) ↔ ∃ j, x = v j ∨ x = -v j := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases h : i.val < 8
    · exact ⟨⟨i, h⟩, Or.inl (by simp [pm16, h])⟩
    · exact ⟨⟨i.val - 8, by omega⟩, Or.inr (by simp [pm16, h])⟩
  · rintro ⟨j, rfl | rfl⟩
    · exact ⟨_, pm16_lo v j⟩
    · exact ⟨_, pm16_hi v j⟩

lemma range_pm16_comp {v : Fin 8 → E5} {σ : Fin 8 → Fin 8} (hσ : Function.Surjective σ) :
    range (pm16 (v ∘ σ)) = range (pm16 v) := by
  ext x
  simp only [mem_range_pm16, Function.comp_apply]
  constructor
  · rintro ⟨j, h⟩; exact ⟨σ j, h⟩
  · rintro ⟨j, h⟩
    obtain ⟨i, rfl⟩ := hσ j
    exact ⟨i, h⟩

/-- Swap the two points of pair `j / 2` when `flip (j / 2)`. -/
def swapIdx (flip : Fin 4 → Bool) (j : Fin 8) : Fin 8 :=
  if flip ⟨j / 2, by omega⟩ then ⟨if j.val % 2 = 0 then j + 1 else j - 1, by split_ifs <;> omega⟩
  else j

lemma swapIdx_invol (flip : Fin 4 → Bool) (j : Fin 8) : swapIdx flip (swapIdx flip j) = j := by
  unfold swapIdx
  by_cases hf : flip ⟨j / 2, by omega⟩ = true
  · rw [if_pos hf]
    have hk : (⟨(if j.val % 2 = 0 then j.val + 1 else j.val - 1) / 2, by split_ifs <;> omega⟩ :
        Fin 4) = ⟨j / 2, by omega⟩ := by ext; simp only; split_ifs <;> omega
    simp only [hk, hf, if_true]
    ext; simp only; split_ifs <;> omega
  · rw [if_neg hf, if_neg hf]

lemma swapIdx_val (flip : Fin 4 → Bool) (j : Fin 8) : (swapIdx flip j).val =
    if flip ⟨j / 2, by omega⟩ then (if j.val % 2 = 0 then j.val + 1 else j.val - 1) else j.val := by
  unfold swapIdx; split_ifs <;> rfl

lemma vp_swap (v : Fin 8 → E5) (flip : Fin 4 → Bool) (k : Fin 4) :
    vp (v ∘ swapIdx flip) k = if flip k then vm v k else vp v k := by
  simp only [vp, vm, Function.comp_apply]
  have hk : (⟨2 * (k : ℕ) / 2, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  by_cases hf : flip k = true
  · rw [if_pos hf]
    congr 1
    ext
    rw [swapIdx_val]
    simp only [hk, hf, if_true]
    rw [if_pos (by omega)]
  · rw [if_neg hf]
    congr 1
    ext
    rw [swapIdx_val]
    simp only [hk, hf, Bool.false_eq_true, if_false]

lemma vm_swap (v : Fin 8 → E5) (flip : Fin 4 → Bool) (k : Fin 4) :
    vm (v ∘ swapIdx flip) k = if flip k then vp v k else vm v k := by
  simp only [vp, vm, Function.comp_apply]
  have hk : (⟨(2 * (k : ℕ) + 1) / 2, by omega⟩ : Fin 4) = k := by ext; simp only; omega
  by_cases hf : flip k = true
  · rw [if_pos hf]
    congr 1
    ext
    rw [swapIdx_val]
    simp only [hk, hf, if_true]
    rw [if_neg (by omega)]
    omega
  · rw [if_neg hf]
    congr 1
    ext
    rw [swapIdx_val]
    simp only [hk, hf, Bool.false_eq_true, if_false]

/-- **The full prism configuration** has at least 243 nonempty faces. -/
theorem prism_core {v : Fin 8 → E5} {u : E5} (hu : ∀ j, ⟪u, v j⟫ = 1) (r : Fin 4 → E5)
    (hr0 : ∀ (k : Fin 4) (j : Fin 8), j.val / 2 ≠ k.val → ⟪r k, v j⟫ = 0)
    (hrp : ∀ k, 0 < ⟪r k, vp v k⟫) (hrm : ∀ k, 0 < ⟪r k, vm v k⟫)
    (hne : ∀ k, vp v k ≠ vm v k) :
    243 ≤ (faces (convexHull ℝ (range (pm16 v)))).ncard := by
  classical
  obtain ⟨w₀, hw₀, hrw₀, α₀, β₀, hdec₀, hαβ₀, hκ₀⟩ := normal_form hr0 hrp hrm hu hne
  -- choose the sign of `w` so that `κ = u(w) ≥ 0`
  obtain ⟨w, α, β, hw, hrw, hdec, hαβ, hκ, hκ0⟩ : ∃ (w : E5) (α β : Fin 4 → ℝ), w ≠ 0 ∧
      (∀ k, ⟪r k, w⟫ = 0) ∧ (∀ k, w = α k • vp v k + β k • vm v k) ∧ (∀ k, α k * β k < 0) ∧
      (∀ k, α k + β k = ⟪u, w⟫) ∧ 0 ≤ ⟪u, w⟫ := by
    by_cases h : 0 ≤ ⟪u, w₀⟫
    · exact ⟨w₀, α₀, β₀, hw₀, hrw₀, hdec₀, hαβ₀, hκ₀, h⟩
    · refine ⟨-w₀, -α₀, -β₀, neg_ne_zero.2 hw₀, fun k => by rw [inner_neg_right, hrw₀, neg_zero],
        fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
      · rw [hdec₀ k]; simp [neg_smul]; abel
      · simpa [neg_mul_neg] using hαβ₀ k
      · simp only [Pi.neg_apply, inner_neg_right, ← hκ₀ k]; ring
      · rw [inner_neg_right]; linarith
  set κ := ⟪u, w⟫ with hκdef
  -- unoriented realization
  have hreal0 : ∀ (x : ℝ) (ξp ξm : Fin 4 → ℝ), (∀ k, α k * ξp k + β k * ξm k = x) →
      ∃ z : E5, ∀ k, ⟪z, vp v k⟫ = ξp k ∧ ⟪z, vm v k⟫ = ξm k := by
    intro x ξp ξm hx
    obtain ⟨z, hzw, hzm⟩ := exists_z hr0 hrp hrm hw hrw x ξm
    refine ⟨z, fun k => ⟨?_, hzm k⟩⟩
    have h1 := congrArg (fun y => ⟪z, y⟫) (hdec k)
    simp only [inner_add_right, real_inner_smul_right, hzw, hzm] at h1
    have hα : α k ≠ 0 := fun h => by have := hαβ k; rw [h, zero_mul] at this; exact lt_irrefl _ this
    have h2 := hx k
    have : α k * ⟪z, vp v k⟫ = α k * ξp k := by linarith
    exact mul_left_cancel₀ hα this
  -- orient each pair
  set flip : Fin 4 → Bool := fun k => decide (α k < 0) with hflip
  set v' := v ∘ swapIdx flip with hv'
  set A : Fin 4 → ℝ := fun k => if flip k then β k else α k with hA
  set B : Fin 4 → ℝ := fun k => if flip k then α k else β k with hB
  have hApos : ∀ k, 0 < A k ∧ B k < 0 := by
    intro k
    have h := hαβ k
    by_cases hk : α k < 0
    · have hf : flip k = true := by simp [hflip, hk]
      have e1 : A k = β k := by simp [hA, hf]
      have e2 : B k = α k := by simp [hB, hf]
      rw [e1, e2]
      exact ⟨by nlinarith, hk⟩
    · have hf : flip k = false := by simp [hflip, hk]
      have e1 : A k = α k := by simp [hA, hf]
      have e2 : B k = β k := by simp [hB, hf]
      rw [e1, e2]
      have hα0 : α k ≠ 0 := fun e => by rw [e, zero_mul] at h; exact lt_irrefl _ h
      have hα : 0 < α k := lt_of_le_of_ne (not_lt.1 hk) (Ne.symm hα0)
      exact ⟨hα, by nlinarith⟩
  have hAB : ∀ k, A k + B k = κ := by
    intro k; simp only [hA, hB]; split_ifs
    · rw [add_comm]; exact hκ k
    · exact hκ k
  have hreal : ∀ (x : ℝ) (Xp Xm : Fin 4 → ℝ), (∀ k, A k * Xp k + B k * Xm k = x) →
      ∃ z : E5, ∀ k, ⟪z, vp v' k⟫ = Xp k ∧ ⟪z, vm v' k⟫ = Xm k := by
    intro x Xp Xm hx
    obtain ⟨z, hz⟩ := hreal0 x (fun k => if flip k then Xm k else Xp k)
      (fun k => if flip k then Xp k else Xm k) (fun k => by
        have := hx k; simp only [hA, hB] at this ⊢; split_ifs at this ⊢ <;> linarith)
    refine ⟨z, fun k => ?_⟩
    rw [hv', vp_swap, vm_swap]
    have := hz k
    by_cases hk : flip k = true
    · simp only [hk, if_true] at this ⊢; exact ⟨this.2, this.1⟩
    · simp only [hk, Bool.false_eq_true, if_false] at this ⊢; exact this
  have hrange : range (pm16 v') = range (pm16 v) :=
    range_pm16_comp (Function.LeftInverse.surjective (swapIdx_invol flip))
  rw [← hrange]
  rcases eq_or_lt_of_le hκ0 with h0 | hpos
  · -- parallel
    refine faces_parallel (A := A) (fun k => (hApos k).1) fun x Xp Xm hx => hreal x Xp Xm ?_
    intro k
    have hB' : B k = -A k := by have := hAB k; rw [← h0] at this; linarith
    rw [hB']; exact hx k
  · exact faces_concurrent hpos (fun k => (hApos k).1) (fun k => (hApos k).2) hAB hreal

end Kalai5.FullPrism
