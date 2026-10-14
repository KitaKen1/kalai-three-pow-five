import Kalai5.Cert.Engine2
import Kalai5.Endpoints.FullRidge

/-!
# Certificate engine with full-facet features

A cost `χ : Cost3` is a `Cost2` plus, on the rows with `n = 8` (full facets at sixteen
vertices), the term `a8 + q8 r`.  The summed cost then involves `cnt8 rows` (the number of full
facets, `2 kP`) and `sumR8 rows` (the number of their ridges), which the ridge count
`IsCSPolytope5.full_ridge_rows` bounds.
-/

namespace Kalai5

/-- A cost with full-facet terms. -/
structure Cost3 where
  ψ : Cost2
  a8 : ℤ
  q8 : ℤ

namespace Cost3

/-- The cost of a row. -/
def eval (χ : Cost3) (R : Row) : ℤ :=
  χ.ψ.eval R + (if R.n = 8 then χ.a8 + χ.q8 * R.r else 0)

lemma sum_eval (χ : Cost3) (rows : List Row) :
    (rows.map χ.eval).sum = (rows.map χ.ψ.eval).sum + χ.a8 * (cnt8 rows : ℕ) +
      χ.q8 * (sumR8 rows : ℕ) := by
  induction rows with
  | nil => simp [cnt8, sumR8]
  | cons R rs ih =>
    simp only [cnt8, sumR8] at ih
    simp only [List.map_cons, List.sum_cons, cnt8, sumR8, List.filter_cons, ih, eval]
    by_cases h : R.n = 8 <;> simp [h] <;> push_cast <;> ring

/-- The cost is nonnegative on the admissible small rows. -/
def checkSmall (χ : Cost3) (nmax : ℕ) (Gcap : ℤ) (excl : List Row) : Bool :=
  Cost.smallAll.all fun R => decide (R.n ≤ nmax → 2 * R.g ≤ Gcap → R ∉ excl → 0 ≤ χ.eval R)

lemma nonneg_of_checkSmall {χ : Cost3} {nmax : ℕ} {Gcap : ℤ} {excl : List Row}
    (hc : χ.checkSmall nmax Gcap excl = true) {R : Row} (hR : RowOK nmax Gcap excl R)
    (h7 : R.n ≤ 7 ∨ R.r ≤ 7) : 0 ≤ χ.eval R := by
  have hmem : R ∈ Cost.smallAll := by
    rcases h7 with h | h
    · exact List.mem_append_left _ (hR.small h)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨R.dual, hR.smalld h, Row.dual_dual R⟩)
  have := List.all_eq_true.1 hc R hmem
  exact (of_decide_eq_true this) hR.n_le hR.g_le hR.notex

/-- **Nonnegativity of the summed cost** from the two checks. -/
theorem sum_nonneg {χ : Cost3} {nmax : ℕ} {Gcap : ℤ} {excl : List Row} {rows : List Row}
    (hrows : ∀ R ∈ rows, RowOK nmax Gcap excl R) (hc : χ.checkSmall nmax Gcap excl = true)
    (hbox : ∀ R, RowOK nmax Gcap excl R → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ χ.ψ.φ.aff R + (if χ.ψ.τ < 2 * R.g then χ.ψ.ag else 0) +
        (if R.n = 8 then χ.a8 + χ.q8 * R.r else 0)) :
    0 ≤ (rows.map χ.eval).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
  by_cases h7 : R.n ≤ 7 ∨ R.r ≤ 7
  · exact nonneg_of_checkSmall hc (hrows R hR) h7
  · push Not at h7
    rw [eval, Cost2.eval, Cost.eval_of_ge (by omega) (by omega)]
    exact hbox R (hrows R hR) (by omega) (by omega)

end Cost3

namespace Ctx

variable {v h nF nS : ℕ} {excl exclS : List Row} (C : Ctx v h nF nS excl exclS)

/-- **Facet side with a cap, a threshold indicator and full-facet terms.** -/
theorem facet_ineq3 (χ : Cost3) {Gc : ℤ} (hcap : ∀ R ∈ C.F.rows, 2 * R.g ≤ Gc)
    (hc : χ.checkSmall nF Gc excl = true)
    (hbox : ∀ R, RowOK nF Gc excl R → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ χ.ψ.φ.aff R + (if χ.ψ.τ < 2 * R.g then χ.ψ.ag else 0) +
        (if R.n = 8 then χ.a8 + χ.q8 * R.r else 0)) :
    0 ≤ χ.ψ.φ.c0 * (C.D.h : ℤ) + χ.ψ.φ.cn * (C.D.I : ℤ) + χ.ψ.φ.ce * (C.D.f14 : ℤ)
      + χ.ψ.φ.cp * (C.D.y : ℤ) + χ.ψ.φ.cr * (2 * (C.D.r : ℤ)) + χ.ψ.φ.cJ * (2 * (C.D.f03 : ℤ))
      + χ.ψ.φ.a5 * (C.nF5 : ℤ) + χ.ψ.φ.a6 * (C.nF6 : ℤ) + χ.ψ.φ.b5 * (C.rF5 : ℤ)
      + χ.ψ.φ.b6 * (C.rF6 : ℤ) + χ.ψ.ag * (cntBig C.F.rows χ.ψ.τ : ℤ)
      + χ.a8 * (cnt8 C.F.rows : ℤ) + χ.q8 * (sumR8 C.F.rows : ℤ) := by
  have hrows : ∀ R ∈ C.F.rows, RowOK nF Gc excl R := fun R hR =>
    { C.rowF R hR with g_le := hcap R hR }
  have h1 := Cost3.sum_nonneg hrows hc hbox
  rw [Cost3.sum_eval, Cost2.sum_eval, Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e,
    C.F.sum_p, C.F.sum_r, C.F.sum_J] at h1
  push_cast at h1
  exact h1

end Ctx

end Kalai5
