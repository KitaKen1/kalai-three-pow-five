import Kalai5.Cert.Engine
import Kalai5.Cert.Pair

/-!
# Certificate engine with a threshold indicator on `g`

A cost `ψ : Cost2` is a `Cost` plus an indicator `[τ < 2g]` with coefficient `ag`.  Inside a leaf
where every facet row has `2g ≤ Gc` (a cap below the cell bound on `G`), the summed cost gives a
linear inequality in the flag numbers, the four counts of `Cost`, and `cntBig rows τ`, the number
of rows with `τ < 2g`; the two-facet bound (`IsCSPolytope5.cntBig_le_two`) caps the latter by `2`.
-/

namespace Kalai5

/-- A cost with a threshold indicator on `g`. -/
structure Cost2 where
  φ : Cost
  ag : ℤ
  τ : ℤ

namespace Cost2

/-- The cost of a row. -/
def eval (ψ : Cost2) (R : Row) : ℤ := ψ.φ.eval R + (if ψ.τ < 2 * R.g then ψ.ag else 0)

lemma sum_eval (ψ : Cost2) (rows : List Row) :
    (rows.map ψ.eval).sum = (rows.map ψ.φ.eval).sum + ψ.ag * (cntBig rows ψ.τ : ℕ) := by
  induction rows with
  | nil => simp [cntBig]
  | cons R rs ih =>
    simp only [cntBig] at ih
    simp only [List.map_cons, List.sum_cons, cntBig, List.filter_cons, ih, eval]
    by_cases h : ψ.τ < 2 * R.g <;> simp [h] <;> push_cast <;> ring

/-- The cost is nonnegative on the admissible small rows. -/
def checkSmall (ψ : Cost2) (nmax : ℕ) (Gcap : ℤ) (excl : List Row) : Bool :=
  Cost.smallAll.all fun R => decide (R.n ≤ nmax → 2 * R.g ≤ Gcap → R ∉ excl → 0 ≤ ψ.eval R)

lemma nonneg_of_checkSmall {ψ : Cost2} {nmax : ℕ} {Gcap : ℤ} {excl : List Row}
    (hc : ψ.checkSmall nmax Gcap excl = true) {R : Row} (hR : RowOK nmax Gcap excl R)
    (h7 : R.n ≤ 7 ∨ R.r ≤ 7) : 0 ≤ ψ.eval R := by
  have hmem : R ∈ Cost.smallAll := by
    rcases h7 with h | h
    · exact List.mem_append_left _ (hR.small h)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨R.dual, hR.smalld h, Row.dual_dual R⟩)
  have := List.all_eq_true.1 hc R hmem
  exact (of_decide_eq_true this) hR.n_le hR.g_le hR.notex

/-- **Nonnegativity of the summed cost** from the two checks. -/
theorem sum_nonneg {ψ : Cost2} {nmax : ℕ} {Gcap : ℤ} {excl : List Row} {rows : List Row}
    (hrows : ∀ R ∈ rows, RowOK nmax Gcap excl R) (hc : ψ.checkSmall nmax Gcap excl = true)
    (hbox : ∀ R, RowOK nmax Gcap excl R → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ ψ.φ.aff R + (if ψ.τ < 2 * R.g then ψ.ag else 0)) :
    0 ≤ (rows.map ψ.eval).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
  by_cases h7 : R.n ≤ 7 ∨ R.r ≤ 7
  · exact nonneg_of_checkSmall hc (hrows R hR) h7
  · push_neg at h7
    rw [eval, Cost.eval_of_ge (by omega) (by omega)]
    exact hbox R (hrows R hR) (by omega) (by omega)

end Cost2

/-- Case split on the maximal `g`: some row has `g ≥ k`, or all rows have `2g ≤ 2k - 2`. -/
lemma rows_split_max (rows : List Row) (k : ℤ) :
    (∃ R ∈ rows, k ≤ R.g) ∨ (∀ R ∈ rows, 2 * R.g ≤ 2 * k - 2) := by
  by_cases h : ∃ R ∈ rows, k ≤ R.g
  · exact Or.inl h
  · push_neg at h
    exact Or.inr fun R hR => by have := h R hR; omega

/-- Below the cap there is nothing to count. -/
lemma cntBig_le_of_cap {rows : List Row} {τ : ℤ} (h : ∀ R ∈ rows, 2 * R.g ≤ τ) :
    cntBig rows τ ≤ 2 := by
  have : cntBig rows τ = 0 := by
    unfold cntBig
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro R hR
    simp only [decide_eq_true_eq, not_lt]
    exact h R hR
  omega

namespace Ctx

variable {v h nF nS : ℕ} {excl exclS : List Row} (C : Ctx v h nF nS excl exclS)

/-- **Facet side with a cap and a threshold indicator.** -/
theorem facet_ineq2 (ψ : Cost2) {Gc : ℤ} (hcap : ∀ R ∈ C.F.rows, 2 * R.g ≤ Gc)
    (hc : ψ.checkSmall nF Gc excl = true)
    (hbox : ∀ R, RowOK nF Gc excl R → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ ψ.φ.aff R + (if ψ.τ < 2 * R.g then ψ.ag else 0)) :
    0 ≤ ψ.φ.c0 * (C.D.h : ℤ) + ψ.φ.cn * (C.D.I : ℤ) + ψ.φ.ce * (C.D.f14 : ℤ)
      + ψ.φ.cp * (C.D.y : ℤ) + ψ.φ.cr * (2 * (C.D.r : ℤ)) + ψ.φ.cJ * (2 * (C.D.f03 : ℤ))
      + ψ.φ.a5 * (C.nF5 : ℤ) + ψ.φ.a6 * (C.nF6 : ℤ) + ψ.φ.b5 * (C.rF5 : ℤ)
      + ψ.φ.b6 * (C.rF6 : ℤ) + ψ.ag * (cntBig C.F.rows ψ.τ : ℤ) := by
  have hrows : ∀ R ∈ C.F.rows, RowOK nF Gc excl R := fun R hR =>
    { C.rowF R hR with g_le := hcap R hR }
  have h1 := Cost2.sum_nonneg hrows hc hbox
  rw [Cost2.sum_eval, Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r,
    C.F.sum_J] at h1
  push_cast at h1
  exact h1

/-- **Polar side with a cap and a threshold indicator.** -/
theorem polar_ineq2 (ψ : Cost2) {Sc : ℤ} (hcap : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ Sc)
    (hc : ψ.checkSmall nS Sc exclS = true)
    (hbox : ∀ R, RowOK nS Sc exclS R → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ ψ.φ.aff R + (if ψ.τ < 2 * R.g then ψ.ag else 0)) :
    0 ≤ ψ.φ.c0 * (C.D.v : ℤ) + ψ.φ.cn * (C.D.I : ℤ) + ψ.φ.ce * (C.D.f03 : ℤ)
      + ψ.φ.cp * (C.D.x : ℤ) + ψ.φ.cr * (2 * (C.D.e : ℤ)) + ψ.φ.cJ * (2 * (C.D.f14 : ℤ))
      + ψ.φ.a5 * (C.nS5 : ℤ) + ψ.φ.a6 * (C.nS6 : ℤ) + ψ.φ.b5 * (C.rS5 : ℤ)
      + ψ.φ.b6 * (C.rS6 : ℤ) + ψ.ag * (cntBig C.Fs.rows ψ.τ : ℤ) := by
  have hrows : ∀ R ∈ C.Fs.rows, RowOK nS Sc exclS R := fun R hR =>
    { C.rowFs R hR with g_le := hcap R hR }
  have h1 := Cost2.sum_nonneg hrows hc hbox
  rw [Cost2.sum_eval, Cost.sum_eval, C.Fs.length_eq, C.Fs.sum_n, C.Fs.sum_e, C.Fs.sum_p,
    C.Fs.sum_r, C.Fs.sum_J, C.rel.h, C.rel.I, C.rel.f14, C.rel.y, C.rel.r, C.rel.f03] at h1
  push_cast at h1
  exact h1

end Ctx

end Kalai5
