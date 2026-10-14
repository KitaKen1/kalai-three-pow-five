import Kalai5.Cube3.Config
import Kalai5.LemmaB.Planar

/-! The five possible fibre sizes and the absence of a common zero-width direction. -/

namespace Kalai5.Cube3

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

def cls (j : Fin 4) : Finset (Fin 8) := Finset.univ.filter fun v => C.c v = j

lemma cls_nonempty (j : Fin 4) : (C.cls j).Nonempty := by
  obtain ⟨v, hv⟩ := C.surj j
  exact ⟨v, by simp [cls, hv]⟩

lemma sum_card_cls : ∑ j : Fin 4, (C.cls j).card = 8 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := C.c) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simpa only [cls, Finset.card_univ, Fintype.card_fin] using h.symm

lemma card_fibre (j : Fin 4) : (fibre C.c C.k j).card = (C.cls j).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw h
  have hv' : C.c v = j := by simpa [cls] using hv
  have hw' : C.c w = j := by simpa [cls] using hw
  exact C.inj v w (hv'.trans hw'.symm) h

lemma convpos_fibre (j : Fin 4) :
    ∀ p ∈ fibre C.c C.k j, p ∈ (convexHull ℝ (fibre C.c C.k j : Set (E 2))).extremePoints ℝ := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hp
  have hv' : C.c v = j := by simpa using hv
  simpa only [hv'] using C.convpos v

lemma dim_fibre_eq_two {j : Fin 4} (h3 : 3 ≤ (C.cls j).card) :
    dim (convexHull ℝ (fibre C.c C.k j : Set (E 2))) = 2 :=
  LemmaB.dim_eq_two_of_convpos (C.convpos_fibre j) (by rw [C.card_fibre]; exact h3)

/-- The ordering is only bookkeeping: no unproved permutation symmetry of the
balanced offsets is used. -/
theorem five_size_patterns : ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card = 5 ∧ (C.cls (τ 1)).card = 1 ∧
      (C.cls (τ 2)).card = 1 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 4 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 1 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 3 ∧
      (C.cls (τ 2)).card = 1 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 3 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 2 ∧ (C.cls (τ 3)).card = 1) ∨
    ((C.cls (τ 0)).card = 2 ∧ (C.cls (τ 1)).card = 2 ∧
      (C.cls (τ 2)).card = 2 ∧ (C.cls (τ 3)).card = 2) := by
  let f : Fin 4 → ℕ := fun j => (C.cls j).card
  let τ : Equiv.Perm (Fin 4) := Fin.revPerm.trans (Tuple.sort f)
  have hm := Tuple.monotone_sort f
  have h01 : f (τ 1) ≤ f (τ 0) := hm (show Fin.rev (1 : Fin 4) ≤ Fin.rev 0 by decide)
  have h12 : f (τ 2) ≤ f (τ 1) := hm (show Fin.rev (2 : Fin 4) ≤ Fin.rev 1 by decide)
  have h23 : f (τ 3) ≤ f (τ 2) := hm (show Fin.rev (3 : Fin 4) ≤ Fin.rev 2 by decide)
  have hsum : ∑ i : Fin 4, f (τ i) = 8 := by
    rw [Equiv.sum_comp τ]
    exact C.sum_card_cls
  rw [Fin.sum_univ_four] at hsum
  have hp : 0 < f (τ 3) := Finset.card_pos.2 (C.cls_nonempty (τ 3))
  refine ⟨τ, ?_⟩
  change (f (τ 0) = 5 ∧ f (τ 1) = 1 ∧ f (τ 2) = 1 ∧ f (τ 3) = 1) ∨
    (f (τ 0) = 4 ∧ f (τ 1) = 2 ∧ f (τ 2) = 1 ∧ f (τ 3) = 1) ∨
    (f (τ 0) = 3 ∧ f (τ 1) = 3 ∧ f (τ 2) = 1 ∧ f (τ 3) = 1) ∨
    (f (τ 0) = 3 ∧ f (τ 1) = 2 ∧ f (τ 2) = 2 ∧ f (τ 3) = 1) ∨
    (f (τ 0) = 2 ∧ f (τ 1) = 2 ∧ f (τ 2) = 2 ∧ f (τ 3) = 2)
  omega

/-- A common zero-width direction either kills all vertices or produces an
extra full normal after rescaling its four class offsets. -/
theorem span_of_no_extra (hno : ¬ C.ExtraPM) (b : E 2)
    (hb : ∀ v w, C.c v = C.c w → ⟪b, C.k v⟫ = ⟪b, C.k w⟫) : b = 0 := by
  classical
  let rep : Fin 4 → Fin 8 := fun j => (C.surj j).choose
  have hrep : ∀ j, C.c (rep j) = j := fun j => (C.surj j).choose_spec
  let f : Fin 4 → ℝ := fun j => ⟪b, C.k (rep j)⟫
  have he : ∀ v, ⟪b, C.k v⟫ = f (C.c v) := fun v => hb v (rep (C.c v)) (hrep _).symm
  by_cases hf : Balanced f
  · apply C.faithful (fun j => -f j) (by unfold Balanced at *; dsimp; linarith) b
    intro v
    rw [he]
    ring
  · by_contra hb0
    have hd : f 0 + f 3 - f 1 - f 2 ≠ 0 := by
      intro hd0
      apply hf
      unfold Balanced
      linarith only [hd0]
    let t : ℝ := 2 / (f 0 + f 3 - f 1 - f 2)
    have ht : t * (f 0 + f 3 - f 1 - f 2) = 2 := div_mul_cancel₀ _ hd
    have ht0 : t ≠ 0 := by intro h; rw [h, zero_mul] at ht; norm_num at ht
    let s : Fin 4 → ℝ := ![1, 1, -1, 1]
    let a : Fin 4 → ℝ := fun j => s j - t * f j
    have ha : Balanced a := by
      dsimp [Balanced, a, s]
      nlinarith [ht]
    apply hno
    refine ⟨a, t • b, ha, smul_ne_zero ht0 hb0, fun v => ?_⟩
    have hv : a (C.c v) + ⟪t • b, C.k v⟫ = s (C.c v) := by
      rw [real_inner_smul_left, he]
      dsimp [a]
      ring
    rw [hv]
    have hs : ∀ j, s j = 1 ∨ s j = -1 := by intro j; fin_cases j <;> norm_num [s]
    exact hs (C.c v)

end Config

end Kalai5.Cube3
