import Kalai5.Cert.EngineW

/-! Generated exact certificate leaves; see design_scripts/cert/emit_cover20.py. -/

namespace Kalai5.E20w

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma box_F_k2_g6s0 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨30, -14, 5, 0, -6, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 19, 21, 10, 44⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx3 : R ≠ ⟨8, 20, 23, 11, 47⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨30, -14, 5, 0, -6, 1, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

lemma box_S_k2_g6s0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-19290, 5787, 0, 0, 5787, -1929, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-19290, 5787, 0, 0, 5787, -1929, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (0 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 0)
    (hA : C.D.A = 0)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨30, -14, 5, 0, -6, 1, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-19290, 5787, 0, 0, 5787, -1929, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s0
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s2 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 12 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 12 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s2 : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (2 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩, 0, 1000000⟩, 12, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s2
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s2
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 1000000 := by positivity
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 1000000 := by positivity
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j0k0 : ∀ R, RowOK 8 0 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-165, 0, 44, 0, 77, -33, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -11 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 19, 21, 10, 44⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-165, 0, 44, 0, 77, -33, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -11 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j0k0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-310, 65, 24, 0, 109, -39, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-310, 65, 24, 0, 109, -39, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j0k0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 0)
    (hcntF : cntBig C.F.rows 6 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0)
    (hcntS : cntBig C.Fs.rows 4 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-165, 0, 44, 0, 77, -33, 0, 0, 0, 0⟩, 0, 6⟩, -11, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j0k0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-310, 65, 24, 0, 109, -39, 0, 0, 0, 0⟩, 0, 4⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j0k0
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 6 := by positivity
  have cF2 : (cntBig C.F.rows 6 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 4 := by positivity
  have cS2 : (cntBig C.Fs.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j0k1 : ∀ R, RowOK 8 0 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-6845, 1008, 286, 0, 2377, -647, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -361 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-6845, 1008, 286, 0, 2377, -647, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -361 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j0k1 : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j0k1 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 0)
    (hcntF : cntBig C.F.rows 6 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2)
    (hcntS : cntBig C.Fs.rows 2 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-6845, 1008, 286, 0, 2377, -647, 0, 0, 0, 0⟩, 0, 6⟩, -361, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j0k1
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 2⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j0k1
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 6 := by positivity
  have cF2 : (cntBig C.F.rows 6 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 2 := by positivity
  have cS2 : (cntBig C.Fs.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j0k2 : ∀ R, RowOK 8 0 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-7390, 1602, 615, 0, 2586, -985, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 19, 21, 10, 44⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx2 : R ≠ ⟨8, 20, 23, 11, 47⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-7390, 1602, 615, 0, 2586, -985, 0, 0, 0, 0⟩ : Cost).aff R + (if (6 : ℤ) < 2 * R.g then 0 else 0) +
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

lemma box_S_k2_g6s4_j0k2 : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 1132, -1276, -247, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 1132, -1276, -247, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j0k2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 0)
    (hcntF : cntBig C.F.rows 6 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4)
    (hcntS : cntBig C.Fs.rows 0 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-7390, 1602, 615, 0, 2586, -985, 0, 0, 0, 0⟩, 0, 6⟩, 0, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j0k2
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 1132, -1276, -247, 0, 0, 0, 0⟩, 0, 0⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j0k2
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 6 := by positivity
  have cF2 : (cntBig C.F.rows 6 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 0 := by positivity
  have cS2 : (cntBig C.Fs.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j1k0 : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-1765, 411, 32, 0, 558, -170, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 115 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-1765, 411, 32, 0, 558, -170, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 115 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j1k0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨1030, -309, 0, 0, -309, 103, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨1030, -309, 0, 0, -309, 103, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j1k0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2)
    (hcntF : cntBig C.F.rows 4 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0)
    (hcntS : cntBig C.Fs.rows 4 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-1765, 411, 32, 0, 558, -170, 0, 0, 0, 0⟩, 0, 4⟩, 115, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j1k0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨1030, -309, 0, 0, -309, 103, 0, 0, 0, 0⟩, 0, 4⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j1k0
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 4 := by positivity
  have cF2 : (cntBig C.F.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 4 := by positivity
  have cS2 : (cntBig C.Fs.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j1k1 : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1080 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1080 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j1k1 : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j1k1 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2)
    (hcntF : cntBig C.F.rows 4 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2)
    (hcntS : cntBig C.Fs.rows 2 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩, 0, 4⟩, 1080, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j1k1
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩, 0, 2⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j1k1
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 4 := by positivity
  have cF2 : (cntBig C.F.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 2 := by positivity
  have cS2 : (cntBig C.Fs.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j1k2 : ∀ R, RowOK 8 2 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1080 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 1080 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j1k2 : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j1k2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2)
    (hcntF : cntBig C.F.rows 4 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4)
    (hcntS : cntBig C.Fs.rows 0 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-14765, 3386, 287, 0, 4753, -1440, 0, 0, 0, 0⟩, 0, 4⟩, 1080, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j1k2
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨7930, -2379, 0, 0, -2379, 793, 0, 0, 0, 0⟩, 0, 0⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j1k2
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 4 := by positivity
  have cF2 : (cntBig C.F.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 0 := by positivity
  have cS2 : (cntBig C.Fs.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j2k0 : ∀ R, RowOK 8 4 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-2435, -3271, 928, 0, 1902, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1415 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-2435, -3271, 928, 0, 1902, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -1415 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j2k0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-26570, 7449, 0, -20, 8159, -2553, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-26570, 7449, 0, -20, 8159, -2553, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j2k0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4)
    (hcntF : cntBig C.F.rows 2 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0)
    (hcntS : cntBig C.Fs.rows 4 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-2435, -3271, 928, 0, 1902, 0, 0, 0, 0, 0⟩, 0, 2⟩, -1415, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j2k0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-26570, 7449, 0, -20, 8159, -2553, 0, 0, 0, 0⟩, 0, 4⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j2k0
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 2 := by positivity
  have cF2 : (cntBig C.F.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 4 := by positivity
  have cS2 : (cntBig C.Fs.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j2k1 : ∀ R, RowOK 8 4 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-760, 126, 39, 0, 264, -79, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 52 else 0) +
      (if R.n = 8 then 46 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-760, 126, 39, 0, 264, -79, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 52 else 0) +
      (if R.n = 8 then 46 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j2k1 : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩ : Cost).aff R + (if (2 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j2k1 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4)
    (hcntF : cntBig C.F.rows 2 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2)
    (hcntS : cntBig C.Fs.rows 2 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-760, 126, 39, 0, 264, -79, 0, 0, 0, 0⟩, 52, 2⟩, 46, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j2k1
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩, 0, 2⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j2k1
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 2 := by positivity
  have cF2 : (cntBig C.F.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 2 := by positivity
  have cS2 : (cntBig C.Fs.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

end Kalai5.E20w
