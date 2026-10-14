import Kalai5.Cert.EngineW

/-! Generated exact certificate leaves; see design_scripts/cert/emit_cover20.py. -/

namespace Kalai5.E20w

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma box_F_k2_g6s4_j2k2 : ∀ R, RowOK 8 4 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

lemma box_S_k2_g6s4_j2k2 : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j2k2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4)
    (hcntF : cntBig C.F.rows 2 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4)
    (hcntS : cntBig C.Fs.rows 0 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-760, 126, 39, 0, 264, -79, 0, 0, 0, 0⟩, 52, 2⟩, 46, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j2k2
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 28, -28, -7, 0, 0, 0, 0⟩, 0, 0⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j2k2
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 2 := by positivity
  have cF2 : (cntBig C.F.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 0 := by positivity
  have cS2 : (cntBig C.Fs.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j3k0 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨155, -116, 44, 0, -15, 3, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -19 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hx0 : R ≠ ⟨8, 18, 18, 8, 38⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hx1 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨155, -116, 44, 0, -15, 3, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -19 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s4_j3k0 : ∀ R, RowOK 10 0 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-410, 107, 16, 0, 123, -45, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-410, 107, 16, 0, 123, -45, 0, 0, 0, 0⟩ : Cost).aff R + (if (4 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j3k0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6)
    (hcntF : cntBig C.F.rows 0 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0)
    (hcntS : cntBig C.Fs.rows 4 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨155, -116, 44, 0, -15, 3, 0, 0, 0, 0⟩, 0, 0⟩, -19, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j3k0
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨-410, 107, 16, 0, 123, -45, 0, 0, 0, 0⟩, 0, 4⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j3k0
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 0 := by positivity
  have cF2 : (cntBig C.F.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 4 := by positivity
  have cS2 : (cntBig C.Fs.rows 4 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j3k1 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 6 else 0) +
      (if R.n = 8 then 6 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 6 else 0) +
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

lemma box_S_k2_g6s4_j3k1 : ∀ R, RowOK 10 2 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s4_j3k1 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6)
    (hcntF : cntBig C.F.rows 0 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2)
    (hcntS : cntBig C.Fs.rows 2 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩, 6, 0⟩, 6, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j3k1
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 2⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j3k1
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 0 := by positivity
  have cF2 : (cntBig C.F.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 2 := by positivity
  have cS2 : (cntBig C.Fs.rows 2 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s4_j3k2 : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 6 else 0) +
      (if R.n = 8 then 6 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 6 else 0) +
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

lemma box_S_k2_g6s4_j3k2 : ∀ R, RowOK 10 4 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Cost).aff R + (if (0 : ℤ) < 2 * R.g then 0 else 0) +
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

theorem leaf_k2_g6s4_j3k2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (4 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 4)
    (hcapF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6)
    (hcntF : cntBig C.F.rows 0 ≤ 2)
    (hcapS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4)
    (hcntS : cntBig C.Fs.rows 0 ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-95, 14, 4, 0, 33, -9, 0, 0, 0, 0⟩, 6, 0⟩, 6, 0⟩, 0⟩) hcapF hJF (by decide +kernel) box_F_k2_g6s4_j3k2
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 0⟩, 0, 0⟩, 0⟩) hcapS hJS (by decide +kernel) box_S_k2_g6s4_j3k2
  dsimp only at f1 f2
  have c8 : (cnt8 C.F.rows : ℤ) = 4 := by exact_mod_cast hc8
  have s8 : (sumR8 C.F.rows : ℤ) ≤ 40 := by exact_mod_cast hs8
  have s80 : (0 : ℤ) ≤ sumR8 C.F.rows := by positivity
  have qw0 : (0 : ℤ) ≤ (C.F.rows.map q55RowWeight).sum := by positivity
  have cF0 : (0 : ℤ) ≤ cntBig C.F.rows 0 := by positivity
  have cF2 : (cntBig C.F.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntF
  have cS0 : (0 : ℤ) ≤ cntBig C.Fs.rows 0 := by positivity
  have cS2 : (cntBig C.Fs.rows 0 : ℤ) ≤ 2 := by exact_mod_cast hcntS
  have e1 := C.G_eq; have e2 := C.Gs_eq; have e3 := C.A_eq; have e4 := C.t_eq
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l20,
    l21, l22, l23, l24, l25⟩ := C.lin
  push_cast at l1 l2 l11
  linarith

lemma box_F_k2_g6s6l : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-215, 2, 20, 0, 85, -21, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-215, 2, 20, 0, 85, -21, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

lemma box_S_k2_g6s6l : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s6l (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : (C.D.y : ℤ) ≤ 284)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-215, 2, 20, 0, 85, -21, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s6l
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s6l
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

lemma box_F_k2_g6s6rl : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-55, 2, 4, 0, 21, -5, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 0 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-55, 2, 4, 0, 21, -5, 0, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
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

lemma box_S_k2_g6s6rl : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s6rl (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : 286 ≤ (C.D.y : ℤ))
    (b1 : (C.D.I : ℤ) ≤ 136)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-55, 2, 4, 0, 21, -5, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s6rl
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s6rl
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

lemma box_F_k2_g6s6rrl : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-378, 6, 24, 0, 96, -21, 48, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -33 + 0 * (R.r : ℤ) else 0) + 1 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hw : (0 : ℤ) ≤ 1 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-378, 6, 24, 0, 96, -21, 48, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -33 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s6rrl : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s6rrl (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : 286 ≤ (C.D.y : ℤ))
    (b1 : 138 ≤ (C.D.I : ℤ))
    (b2 : (C.nF5 : ℤ) ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-378, 6, 24, 0, 96, -21, 48, 0, 0, 0⟩, 0, 1000000⟩, -33, 0⟩, 1⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s6rrl
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s6rrl
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

lemma box_F_k2_g6s6rrr : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨57, -14, 4, 0, 21, -5, -32, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 16 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨57, -14, 4, 0, 21, -5, -32, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 16 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s6rrr : ∀ R, RowOK 10 6 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s6rrr (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (6 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 6)
    (b0 : 286 ≤ (C.D.y : ℤ))
    (b1 : 138 ≤ (C.D.I : ℤ))
    (b2 : 4 ≤ (C.nF5 : ℤ))
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨57, -14, 4, 0, 21, -5, -32, 0, 0, 0⟩, 0, 1000000⟩, 16, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s6rrr
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s6rrr
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

lemma box_F_k2_g6s8l : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨-450, -82, 56, 0, 144, -25, 80, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -85 + 0 * (R.r : ℤ) else 0) + 5 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  by_cases hw0 : R = ⟨8, 18, 18, 8, 40⟩
  · subst R
    norm_num [Cost.aff, Row.g, q55RowWeight, q55ElementaryWeight, excRow, eRow,
      r0Row, r35Row, zRow]
  have hx0 : R ≠ ⟨8, 18, 18, 8, 39⟩ := by
    intro h; apply hR.notex; rw [h]; decide
  have hw : (0 : ℤ) ≤ 5 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨-450, -82, 56, 0, 144, -25, 80, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then -85 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s8l : ∀ R, RowOK 10 8 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s8l (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (8 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 8)
    (b0 : (C.nF5 : ℤ) ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨-450, -82, 56, 0, 144, -25, 80, 0, 0, 0⟩, 0, 1000000⟩, -85, 0⟩, 5⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s8l
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s8l
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

lemma box_F_k2_g6s8r : ∀ R, RowOK 8 6 (tRow :: fake8) R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
    0 ≤ (⟨15, -8, 4, 0, 21, -5, -20, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 10 + 0 * (R.r : ℤ) else 0) + 0 * (q55RowWeight R : ℤ) := by
  intro R hR hJ hn hr
  have hw : (0 : ℤ) ≤ 0 * (q55RowWeight R : ℤ) := by positivity
  have hb : (0 : ℤ) ≤ (⟨15, -8, 4, 0, 21, -5, -20, 0, 0, 0⟩ : Cost).aff R + (if (1000000 : ℤ) < 2 * R.g then 0 else 0) +
      (if R.n = 8 then 10 + 0 * (R.r : ℤ) else 0) := by
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

lemma box_S_k2_g6s8r : ∀ R, RowOK 10 8 fake8 R → 4 * R.r ≤ R.J → 8 ≤ R.n → 8 ≤ R.r →
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

theorem leaf_k2_g6s8r (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG1 : (6 : ℤ) ≤ C.D.G)
    (hG2 : C.D.G ≤ 6)
    (hS1 : (8 : ℤ) ≤ C.D.Gs)
    (hS2 : C.D.Gs ≤ 8)
    (b0 : 4 ≤ (C.nF5 : ℤ))
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have f1 := C.facet_ineqW (w := ⟨⟨⟨⟨15, -8, 4, 0, 21, -5, -20, 0, 0, 0⟩, 0, 1000000⟩, 10, 0⟩, 0⟩) (fun R hR => le_trans (C.rowF R hR).g_le hG2) hJF (by decide +kernel) box_F_k2_g6s8r
  have f2 := C.polar_ineqW (w := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1000000⟩, 0, 0⟩, 0⟩) (fun R hR => le_trans (C.rowFs R hR).g_le hS2) hJS (by decide +kernel) box_S_k2_g6s8r
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

end Kalai5.E20w
