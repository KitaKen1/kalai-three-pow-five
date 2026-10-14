import Kalai5.Cert.EngineW

/-! Generated exact certificate leaves; see design_scripts/cert/emit_cover20.py. -/

namespace Kalai5.E20w

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma box_F_k1_g2s2lr : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-126, 28, 2, 22, 32, -21, 6, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 9 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 20, 9, 42⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx3 : R ≠ ⟨8, 20, 23, 11, 48⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-126, 28, 2, 22, 32, -21, 6, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 9 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s2lr : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s2lr (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (2 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 2)
    (b0 : (C.nF5 : ℤ) ≤ 0)
    (b1 : 62 ≤ (C.D.r : ℤ))
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-126, 28, 2, 22, 32, -21, 6, 0, 0, 0⟩, 0, 1000000⟩, 9, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s2lr
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s2lr
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s2rl : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-14, -4, 2, 2, 20, -5, -6, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-14, -4, 2, 2, 20, -5, -6, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s2rl : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s2rl (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (2 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 2)
    (b0 : 2 ≤ (C.nF5 : ℤ))
    (b1 : (C.D.r : ℤ) ≤ 60)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-14, -4, 2, 2, 20, -5, -6, 0, 0, 0⟩, 0, 1000000⟩, 1, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s2rl
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s2rl
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s2rr : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-60, 12, 2, 13, 22, -13, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 6 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 20, 9, 42⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx3 : R ≠ ⟨8, 20, 23, 11, 48⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-60, 12, 2, 13, 22, -13, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 6 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s2rr : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s2rr (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (2 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 2)
    (b0 : 2 ≤ (C.nF5 : ℤ))
    (b1 : 62 ≤ (C.D.r : ℤ))
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-60, 12, 2, 13, 22, -13, 0, 0, 0, 0⟩, 0, 1000000⟩, 6, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s2rr
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s2rr
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s4l : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨110, -116, 18, 14, 50, -5, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -9 + 0 * (R.r : ℤ) else 0) + 9 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 9 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨110, -116, 18, 14, 50, -5, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -9 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s4l : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s4l (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (b0 : (C.D.r : ℤ) ≤ 60)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨110, -116, 18, 14, 50, -5, 0, 0, 0, 0⟩, 0, 1000000⟩, -9, 0⟩, 9⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s4l
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s4l
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s4r : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-30, 4, 2, 10, 14, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 5 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 20, 9, 42⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx3 : R ≠ ⟨8, 19, 21, 10, 44⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx4 : R ≠ ⟨8, 20, 23, 11, 48⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-30, 4, 2, 10, 14, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 5 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s4r : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s4r (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (b0 : 62 ≤ (C.D.r : ℤ))
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-30, 4, 2, 10, 14, -9, 0, 0, 0, 0⟩, 0, 1000000⟩, 5, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s4r
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s4r
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s6ll : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -21 + 0 * (R.r : ℤ) else 0) + 21 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 21 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -21 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s6ll : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s6ll (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : (C.rS6 : ℤ) ≤ 12)
    (b1 : (C.D.x : ℤ) ≤ 266)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩, 0, 1000000⟩, -21, 0⟩, 21⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s6ll
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s6ll
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s6lr : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 20, 9, 42⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s6lr : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s6lr (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : (C.rS6 : ℤ) ≤ 12)
    (b1 : 268 ≤ (C.D.x : ℤ))
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩, 0, 1000000⟩, -1, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s6lr
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s6lr
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s6rl : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -21 + 0 * (R.r : ℤ) else 0) + 21 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 21 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -21 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s6rl : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s6rl (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : 14 ≤ (C.rS6 : ℤ))
    (b1 : (C.D.x : ℤ) ≤ 266)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨170, -236, 42, 50, 134, -29, 0, 0, 0, 0⟩, 0, 1000000⟩, -21, 0⟩, 21⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s6rl
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s6rl
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s6rr : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 20, 9, 42⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s6rr : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s6rr (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : 14 ≤ (C.rS6 : ℤ))
    (b1 : 268 ≤ (C.D.x : ℤ))
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨0, -8, 2, 4, 8, -3, 0, 0, 0, 0⟩, 0, 1000000⟩, -1, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s6rr
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s6rr
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k1_g2s8 : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨234, -92, 14, 10, 14, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 41 + 0 * (R.r : ℤ) else 0) + 7 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 7 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨234, -92, 14, 10, 14, -3, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 41 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

lemma box_S_k1_g2s8 : ∀ R, RowOK 10 8 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) := by
    have h1 := hR.n_le; have h2 := hR.g_nonneg; have h3 := hR.g_le; have h4 := hR.euler
    have h5 := hR.B4; have h6 := hR.B4d; have h7 := hR.ube
    clear hR hw
    norm_num only [Cost.aff, ite_self, zero_mul, add_zero] <;>
      (try split_ifs) <;> (
    obtain ⟨n, e, p, r, J⟩ := R
    simp +instances only [Cost.aff, Row.g, ne_eq, Row.mk.injEq] at *
    first | omega | (interval_cases n <;> first | omega |
      (have hE : e ≤ 55 := by omega
       interval_cases e <;> omega)))
  exact add_nonneg hb hw

theorem leaf_k1_g2s8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (8 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 8)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨234, -92, 14, 10, 14, -3, 0, 0, 0, 0⟩, 0, 1000000⟩, 41, 0⟩, 7⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s8
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s8
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 2 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 18 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

end Kalai5.E20w
