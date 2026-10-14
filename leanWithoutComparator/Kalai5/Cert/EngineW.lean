import Kalai5.Cert.Engine3
import Kalai5.Endpoints.Q55.RowWeights

/-!
# Certificate costs with full-facet counts and proven Q55 row weights

The row check also accepts `4 r ≤ J`, proved geometrically by
`IsCSPolytope5.facetRows_four_r_le`. Old certificate engines are unchanged.
-/

namespace Kalai5

lemma q55RowWeight_of_box {R : Row} (hn : 8 ≤ R.n) (hr : 8 ≤ R.r) :
    q55RowWeight R = if R = ⟨8, 19, 19, 8, 38⟩ then 1 else q55ElementaryWeight R := by
  have hY : R ≠ excRow := fun h => by rw [h] at hn; norm_num [excRow] at hn
  have hE : R ≠ eRow := fun h => by rw [h] at hn; norm_num [eRow] at hn
  have h0 : R ≠ r0Row := fun h => by rw [h] at hr; norm_num [r0Row] at hr
  have h35 : R ≠ r35Row := fun h => by rw [h] at hr; norm_num [r35Row] at hr
  have h19 : R ≠ zRow := fun h => by rw [h] at hr; norm_num [zRow] at hr
  simp only [q55RowWeight, hY, hE, h0, h35, h19, ite_false]

structure CostW where
  χ : Cost3
  μ : ℤ

namespace CostW

def eval (w : CostW) (R : Row) : ℤ := w.χ.eval R + w.μ * q55RowWeight R

lemma sum_eval (w : CostW) (rows : List Row) :
    (rows.map w.eval).sum = (rows.map w.χ.eval).sum +
      w.μ * ((rows.map q55RowWeight).sum : ℕ) := by
  induction rows with
  | nil => simp
  | cons R rs ih =>
    simp only [List.map_cons, List.sum_cons, ih, eval]
    push_cast
    ring

def checkSmall (w : CostW) (nmax : ℕ) (Gcap : ℤ) (excl : List Row) : Bool :=
  Cost.smallAll.all fun R => decide
    (R.n ≤ nmax → 2 * R.g ≤ Gcap → R ∉ excl → 4 * R.r ≤ R.J → 0 ≤ w.eval R)

lemma nonneg_of_checkSmall {w : CostW} {nmax : ℕ} {Gcap : ℤ} {excl : List Row}
    (hc : w.checkSmall nmax Gcap excl = true) {R : Row} (hR : RowOK nmax Gcap excl R)
    (hJ : 4 * R.r ≤ R.J) (h7 : R.n ≤ 7 ∨ R.r ≤ 7) : 0 ≤ w.eval R := by
  have hmem : R ∈ Cost.smallAll := by
    rcases h7 with h | h
    · exact List.mem_append_left _ (hR.small h)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨R.dual, hR.smalld h, Row.dual_dual R⟩)
  have := List.all_eq_true.1 hc R hmem
  exact (of_decide_eq_true this) hR.n_le hR.g_le hR.notex hJ

theorem sum_nonneg {w : CostW} {nmax : ℕ} {Gcap : ℤ} {excl : List Row} {rows : List Row}
    (hrows : ∀ R ∈ rows, RowOK nmax Gcap excl R) (hJ : ∀ R ∈ rows, 4 * R.r ≤ R.J)
    (hc : w.checkSmall nmax Gcap excl = true)
    (hbox : ∀ R, RowOK nmax Gcap excl R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ w.χ.ψ.φ.aff R + (if w.χ.ψ.τ < 2 * R.g then w.χ.ψ.ag else 0) +
        (if R.n = 8 then w.χ.a8 + w.χ.q8 * R.r else 0) + w.μ * q55RowWeight R) :
    0 ≤ (rows.map w.eval).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
  by_cases h7 : R.n ≤ 7 ∨ R.r ≤ 7
  · exact nonneg_of_checkSmall hc (hrows R hR) (hJ R hR) h7
  · push_neg at h7
    rw [eval, Cost3.eval, Cost2.eval, Cost.eval_of_ge (by omega) (by omega)]
    exact hbox R (hrows R hR) (hJ R hR) (by omega) (by omega)

end CostW

namespace Ctx

variable {v h nF nS : ℕ} {excl exclS : List Row} (C : Ctx v h nF nS excl exclS)

theorem facet_ineqW (w : CostW) {Gc : ℤ} (hcap : ∀ R ∈ C.F.rows, 2 * R.g ≤ Gc)
    (hJ : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J) (hc : w.checkSmall nF Gc excl = true)
    (hbox : ∀ R, RowOK nF Gc excl R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ w.χ.ψ.φ.aff R + (if w.χ.ψ.τ < 2 * R.g then w.χ.ψ.ag else 0) +
        (if R.n = 8 then w.χ.a8 + w.χ.q8 * R.r else 0) + w.μ * q55RowWeight R) :
    0 ≤ w.χ.ψ.φ.c0 * (C.D.h : ℤ) + w.χ.ψ.φ.cn * (C.D.I : ℤ)
      + w.χ.ψ.φ.ce * (C.D.f14 : ℤ) + w.χ.ψ.φ.cp * (C.D.y : ℤ)
      + w.χ.ψ.φ.cr * (2 * (C.D.r : ℤ)) + w.χ.ψ.φ.cJ * (2 * (C.D.f03 : ℤ))
      + w.χ.ψ.φ.a5 * (C.nF5 : ℤ) + w.χ.ψ.φ.a6 * (C.nF6 : ℤ)
      + w.χ.ψ.φ.b5 * (C.rF5 : ℤ) + w.χ.ψ.φ.b6 * (C.rF6 : ℤ)
      + w.χ.ψ.ag * (cntBig C.F.rows w.χ.ψ.τ : ℤ)
      + w.χ.a8 * (cnt8 C.F.rows : ℤ) + w.χ.q8 * (sumR8 C.F.rows : ℤ)
      + w.μ * ((C.F.rows.map q55RowWeight).sum : ℕ) := by
  have hrows : ∀ R ∈ C.F.rows, RowOK nF Gc excl R := fun R hR =>
    { C.rowF R hR with g_le := hcap R hR }
  have h1 := CostW.sum_nonneg hrows hJ hc hbox
  rw [CostW.sum_eval, Cost3.sum_eval, Cost2.sum_eval, Cost.sum_eval,
    C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r, C.F.sum_J] at h1
  generalize ((C.F.rows.map q55RowWeight).sum : ℕ) = QW at h1 ⊢
  push_cast at h1
  exact h1

/-- The same engine on the polar side; its Q55 coefficient can be zero. -/
theorem polar_ineqW (w : CostW) {Gc : ℤ} (hcap : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ Gc)
    (hJ : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J) (hc : w.checkSmall nS Gc exclS = true)
    (hbox : ∀ R, RowOK nS Gc exclS R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
      0 ≤ w.χ.ψ.φ.aff R + (if w.χ.ψ.τ < 2 * R.g then w.χ.ψ.ag else 0) +
        (if R.n = 8 then w.χ.a8 + w.χ.q8 * R.r else 0) + w.μ * q55RowWeight R) :
    0 ≤ w.χ.ψ.φ.c0 * (C.D.v : ℤ) + w.χ.ψ.φ.cn * (C.D.I : ℤ)
      + w.χ.ψ.φ.ce * (C.D.f03 : ℤ) + w.χ.ψ.φ.cp * (C.D.x : ℤ)
      + w.χ.ψ.φ.cr * (2 * (C.D.e : ℤ)) + w.χ.ψ.φ.cJ * (2 * (C.D.f14 : ℤ))
      + w.χ.ψ.φ.a5 * (C.nS5 : ℤ) + w.χ.ψ.φ.a6 * (C.nS6 : ℤ)
      + w.χ.ψ.φ.b5 * (C.rS5 : ℤ) + w.χ.ψ.φ.b6 * (C.rS6 : ℤ)
      + w.χ.ψ.ag * (cntBig C.Fs.rows w.χ.ψ.τ : ℤ)
      + w.χ.a8 * (cnt8 C.Fs.rows : ℤ) + w.χ.q8 * (sumR8 C.Fs.rows : ℤ)
      + w.μ * ((C.Fs.rows.map q55RowWeight).sum : ℕ) := by
  have hrows : ∀ R ∈ C.Fs.rows, RowOK nS Gc exclS R := fun R hR =>
    { C.rowFs R hR with g_le := hcap R hR }
  have h1 := CostW.sum_nonneg hrows hJ hc hbox
  rw [CostW.sum_eval, Cost3.sum_eval, Cost2.sum_eval, Cost.sum_eval,
    C.Fs.length_eq, C.Fs.sum_n, C.Fs.sum_e, C.Fs.sum_p, C.Fs.sum_r, C.Fs.sum_J,
    C.rel.h, C.rel.I, C.rel.f14, C.rel.y, C.rel.r, C.rel.f03] at h1
  generalize ((C.Fs.rows.map q55RowWeight).sum : ℕ) = QW at h1 ⊢
  push_cast at h1
  exact h1

end Ctx

end Kalai5
