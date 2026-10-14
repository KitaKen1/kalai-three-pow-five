import Kalai5.Cert.EngineW

/-! Generated exact certificate leaves; see design_scripts/cert/emit_cover20.py. -/

namespace Kalai5.E20w

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma box_F_k1_rect_g12 : ∀ R, RowOK 8 1000 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-75, -98, 8, 44, 61, -13, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -45 + 0 * (R.r : ℤ) else 0) + 4 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 4 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-75, -98, 8, 44, 61, -13, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -45 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g12 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨10, -3, 0, 0, -3, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨10, -3, 0, 0, -3, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k1_rect_g12 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (12 : ℤ) ≤ C.D.G)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-75, -98, 8, 44, 61, -13, 0, 0, 0, 0⟩, 0, 1000000⟩, -45, 0⟩, 4⟩) (fun R hR => ((C.rowF R hR).capped (by norm_num)).g_le) hJF (by decide +kernel) box_F_k1_rect_g12
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨10, -3, 0, 0, -3, 1, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g12
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

lemma box_F_k1_rect_s12 : ∀ R, RowOK 8 1000 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨998, -472, 58, 62, -2, 11, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 67 + 0 * (R.r : ℤ) else 0) + 29 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw2 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw3 : R = ⟨8, 19, 19, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 29 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨998, -472, 58, 62, -2, 11, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 67 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_s12 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_rect_s12 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (0 : ℤ) ≤ C.D.G)
    (hS1 : (12 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨998, -472, 58, 62, -2, 11, 0, 0, 0, 0⟩, 0, 1000000⟩, 67, 0⟩, 29⟩) (fun R hR => ((C.rowF R hR).capped (by norm_num)).g_le) hJF (by decide +kernel) box_F_k1_rect_s12
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_s12
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

lemma box_F_k1_rect_s10 : ∀ R, RowOK 8 1000 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨274, -104, 14, 10, 2, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 45 + 0 * (R.r : ℤ) else 0) + 7 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw2 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw3 : R = ⟨8, 19, 19, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 7 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨274, -104, 14, 10, 2, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 45 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_s10 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_rect_s10 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (0 : ℤ) ≤ C.D.G)
    (hS1 : (10 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨274, -104, 14, 10, 2, 1, 0, 0, 0, 0⟩, 0, 1000000⟩, 45, 0⟩, 7⟩) (fun R hR => ((C.rowF R hR).capped (by norm_num)).g_le) hJF (by decide +kernel) box_F_k1_rect_s10
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_s10
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

lemma box_F_k1_rect_g0 : ∀ R, RowOK 8 0 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-162, 2, 32, 0, 168, -49, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 47 + 0 * (R.r : ℤ) else 0) + 9 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 19, 19, 8, 38⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 9 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-162, 2, 32, 0, 168, -49, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 47 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g0 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_rect_g0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (0 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 0)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hA : C.D.A = 0)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-162, 2, 32, 0, 168, -49, 0, 0, 0, 0⟩, 0, 1000000⟩, 47, 0⟩, 9⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_rect_g0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g0
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

lemma box_F_k1_rect_g4 : ∀ R, RowOK 8 4 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -3 + 0 * (R.r : ℤ) else 0) + 2 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw1 : R = ⟨8, 19, 19, 8, 39⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  by_cases hw2 : R = ⟨8, 19, 19, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 2 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -3 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g4 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_rect_g4 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (4 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 4)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩, 0, 1000000⟩, -3, 0⟩, 2⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_rect_g4
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g4
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

lemma box_F_k1_rect_g6 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 18 + 0 * (R.r : ℤ) else 0) + 2 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hw : (0 : ℤ) ≤ 2 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 18 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g6 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_rect_g6 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-45, -18, 12, 0, 39, -9, 0, 0, 0, 0⟩, 0, 1000000⟩, 18, 0⟩, 2⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_rect_g6
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g6
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

lemma box_F_k1_rect_g8 : ∀ R, RowOK 8 8 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-25830, 6564, 1902, 0, 20808, -6081, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 26118 + 0 * (R.r : ℤ) else 0) + 317 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 317 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-25830, 6564, 1902, 0, 20808, -6081, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 26118 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g8 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-375, -18, 0, -7, 107, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-375, -18, 0, -7, 107, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k1_rect_g8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (8 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 8)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-25830, 6564, 1902, 0, 20808, -6081, 0, 0, 0, 0⟩, 0, 1000000⟩, 26118, 0⟩, 317⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_rect_g8
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-375, -18, 0, -7, 107, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g8
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

lemma box_F_k1_rect_g10 : ∀ R, RowOK 8 10 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-122256, 34584, 4872, 0, 83181, -24114, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 124470 + 0 * (R.r : ℤ) else 0) + 812 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 812 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-122256, 34584, 4872, 0, 83181, -24114, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 124470 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_rect_g10 : ∀ R, RowOK 10 1000 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-3375, -162, 0, -63, 963, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-3375, -162, 0, -63, 963, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k1_rect_g10 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (10 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 10)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-122256, 34584, 4872, 0, 83181, -24114, 0, 0, 0, 0⟩, 0, 1000000⟩, 124470, 0⟩, 812⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_rect_g10
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-3375, -162, 0, -63, 963, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => ((C.rowFs R hR).capped (by norm_num)).g_le) hJS (by decide +kernel) box_S_k1_rect_g10
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

lemma box_F_k1_g2s0 : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

lemma box_S_k1_g2s0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-224970, 67299, 0, -8, 67499, -22447, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-224970, 67299, 0, -8, 67499, -22447, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k1_g2s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 0)
    (hA : C.D.A = 0)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-224970, 67299, 0, -8, 67499, -22447, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s0
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

lemma box_F_k1_g2s2ll : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-64, 4, 0, 2, 11, -2, 9, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -7 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-64, 4, 0, 2, 11, -2, 9, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -7 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k1_g2s2ll : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k1_g2s2ll (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (2 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 2)
    (hS1 : (2 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 2)
    (b0 : (C.nF5 : ℤ) ≤ 0)
    (b1 : (C.D.r : ℤ) ≤ 60)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-64, 4, 0, 2, 11, -2, 9, 0, 0, 0⟩, 0, 1000000⟩, -7, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k1_g2s2ll
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k1_g2s2ll
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
