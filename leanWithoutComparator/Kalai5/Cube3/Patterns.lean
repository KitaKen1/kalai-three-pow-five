import Kalai5.Cube3.Fibres
import Kalai5.LemmaB.Eight.Pattern

/-! Balanced supporting values yield genuine faces, with distinct sign patterns
counted only once. This is the interface for the finite cube support tables. -/

namespace Kalai5.Cube3

open Set FullPrism LemmaB.Eight

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} (C : Config x)

theorem Config.support_realizable (a : Fin 4 → ℝ) (ha : Balanced a) (b : E 2)
    (M : ℝ) (hM : 0 < M)
    (hbound : ∀ v, |a (C.c v) + ⟪b, C.k v⟫| ≤ M) :
    Realizable8 x (fun v => sgnOf ((a (C.c v) + ⟪b, C.k v⟫) / M)) := by
  obtain ⟨z, hz⟩ := C.real a ha b
  refine ⟨M⁻¹ • z, fun v => (a (C.c v) + ⟪b, C.k v⟫) / M, fun v => ?_, fun v => ?_, rfl⟩
  · change ⟪M⁻¹ • z, x v⟫ = (a (C.c v) + ⟪b, C.k v⟫) / M
    rw [real_inner_smul_left, hz, div_eq_mul_inv, mul_comm]
  · rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).2 (hbound v)

/-- Every counted pattern must have its balanced support witness. No
realizability or support-table completeness is assumed by this interface. -/
theorem Config.card_support_patterns (T : Finset (Fin 8 → ℤ))
    (hT : ∀ s ∈ T, s ≠ 0 ∧ ∃ (a : Fin 4 → ℝ) (b : E 2) (M : ℝ),
      Balanced a ∧ 0 < M ∧ (∀ v, |a (C.c v) + ⟪b, C.k v⟫| ≤ M) ∧
      s = fun v => sgnOf ((a (C.c v) + ⟪b, C.k v⟫) / M)) :
    T.card + 1 ≤ (faces (convexHull ℝ (range (pm16 x)))).ncard := by
  apply card_add_one_le8 T
  intro s hs
  obtain ⟨hne, a, b, M, ha, hM, hb, rfl⟩ := hT s hs
  exact ⟨hne, C.support_realizable a ha b M hM hb⟩

end Kalai5.Cube3
