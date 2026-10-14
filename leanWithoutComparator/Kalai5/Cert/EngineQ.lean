import Kalai5.Cert.Engine
import Kalai5.Endpoints.Z20.QuadLink

/-!
# Certificate engine with the quadrilateral-link term

A cost `χ : CostQ` is a `Cost` plus `μ · qlWeight`, where `qlWeight R = 9 [R = Y] + 4 [R = E]`
(`Y = (7,15,14,6; 29)`, `E = (7,16,16,7; 32)`).  The summed cost over the facet rows of `P` is
linear in the flag numbers, the counts of `Cost`, and `Σ_F qlWeight`, which the
quadrilateral-link inequality (`IsCSPolytope5.quadLink`) bounds by `4A + 2(f₀₂₄ - 3 f₂₄)`.
-/

namespace Kalai5

lemma qlWeight_of_ge {R : Row} (hn : 8 ≤ R.n) : qlWeight R = 0 := by
  have h1 : R ≠ excRow := fun h => by rw [h] at hn; simp [excRow] at hn
  have h2 : R ≠ eRow := fun h => by rw [h] at hn; simp [eRow] at hn
  simp [qlWeight, h1, h2]

/-- A cost with the quadrilateral-link term. -/
structure CostQ where
  φ : Cost
  μ : ℤ

namespace CostQ

/-- The cost of a row. -/
def eval (χ : CostQ) (R : Row) : ℤ := χ.φ.eval R + χ.μ * qlWeight R

lemma sum_eval (χ : CostQ) (rows : List Row) :
    (rows.map χ.eval).sum =
      (rows.map χ.φ.eval).sum + χ.μ * (((rows.map qlWeight).sum : ℕ) : ℤ) := by
  induction rows with
  | nil => simp
  | cons R rs ih =>
    simp only [List.map_cons, List.sum_cons, ih, eval]
    push_cast
    ring

/-- The cost is nonnegative on the admissible small rows. -/
def checkSmall (χ : CostQ) (nmax : ℕ) (Gcap : ℤ) (excl : List Row) : Bool :=
  Cost.smallAll.all fun R => decide (R.n ≤ nmax → 2 * R.g ≤ Gcap → R ∉ excl → 0 ≤ χ.eval R)

lemma nonneg_of_checkSmall {χ : CostQ} {nmax : ℕ} {Gcap : ℤ} {excl : List Row}
    (hc : χ.checkSmall nmax Gcap excl = true) {R : Row} (hR : RowOK nmax Gcap excl R)
    (h7 : R.n ≤ 7 ∨ R.r ≤ 7) : 0 ≤ χ.eval R := by
  have hmem : R ∈ Cost.smallAll := by
    rcases h7 with h | h
    · exact List.mem_append_left _ (hR.small h)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨R.dual, hR.smalld h, Row.dual_dual R⟩)
  have := List.all_eq_true.1 hc R hmem
  exact (of_decide_eq_true this) hR.n_le hR.g_le hR.notex

/-- **Nonnegativity of the summed cost** from the two checks. -/
theorem sum_nonneg {χ : CostQ} {nmax : ℕ} {Gcap : ℤ} {excl : List Row} {rows : List Row}
    (hrows : ∀ R ∈ rows, RowOK nmax Gcap excl R) (hc : χ.checkSmall nmax Gcap excl = true)
    (hbox : ∀ R, RowOK nmax Gcap excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ χ.φ.aff R) :
    0 ≤ (rows.map χ.eval).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
  by_cases h7 : R.n ≤ 7 ∨ R.r ≤ 7
  · exact nonneg_of_checkSmall hc (hrows R hR) h7
  · push_neg at h7
    rw [eval, Cost.eval_of_ge (by omega) (by omega), qlWeight_of_ge (by omega)]
    simpa using hbox R (hrows R hR) (by omega) (by omega)

end CostQ

namespace Ctx

variable {v h nF nS : ℕ} {excl exclS : List Row} (C : Ctx v h nF nS excl exclS)

/-- **Facet side with the quadrilateral-link term.** -/
theorem facet_ineqQ (χ : CostQ) {G2 : ℤ} (hG : C.D.G ≤ G2) (hc : χ.checkSmall nF G2 excl = true)
    (hbox : ∀ R, RowOK nF G2 excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ χ.φ.aff R) :
    0 ≤ χ.φ.c0 * (C.D.h : ℤ) + χ.φ.cn * (C.D.I : ℤ) + χ.φ.ce * (C.D.f14 : ℤ)
      + χ.φ.cp * (C.D.y : ℤ) + χ.φ.cr * (2 * (C.D.r : ℤ)) + χ.φ.cJ * (2 * (C.D.f03 : ℤ))
      + χ.φ.a5 * (C.nF5 : ℤ) + χ.φ.a6 * (C.nF6 : ℤ) + χ.φ.b5 * (C.rF5 : ℤ)
      + χ.φ.b6 * (C.rF6 : ℤ) + χ.μ * (((C.F.rows.map qlWeight).sum : ℕ) : ℤ) := by
  have h1 := CostQ.sum_nonneg (fun R hR => (C.rowF R hR).mono hG) hc hbox
  rw [CostQ.sum_eval, Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r,
    C.F.sum_J] at h1
  generalize ((C.F.rows.map qlWeight).sum : ℕ) = QW at h1 ⊢
  push_cast at h1
  exact h1

/-- **Facet side with the quadrilateral-link term**, without a cell bound on `G`. -/
theorem facet_ineqQ_cap (χ : CostQ) (hn : nF ≤ 11) (hc : χ.checkSmall nF 1000 excl = true)
    (hbox : ∀ R, RowOK nF 1000 excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ χ.φ.aff R) :
    0 ≤ χ.φ.c0 * (C.D.h : ℤ) + χ.φ.cn * (C.D.I : ℤ) + χ.φ.ce * (C.D.f14 : ℤ)
      + χ.φ.cp * (C.D.y : ℤ) + χ.φ.cr * (2 * (C.D.r : ℤ)) + χ.φ.cJ * (2 * (C.D.f03 : ℤ))
      + χ.φ.a5 * (C.nF5 : ℤ) + χ.φ.a6 * (C.nF6 : ℤ) + χ.φ.b5 * (C.rF5 : ℤ)
      + χ.φ.b6 * (C.rF6 : ℤ) + χ.μ * (((C.F.rows.map qlWeight).sum : ℕ) : ℤ) := by
  have h1 := CostQ.sum_nonneg (fun R hR => (C.rowF R hR).capped hn) hc hbox
  rw [CostQ.sum_eval, Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r,
    C.F.sum_J] at h1
  generalize ((C.F.rows.map qlWeight).sum : ℕ) = QW at h1 ⊢
  push_cast at h1
  exact h1

end Ctx

end Kalai5
