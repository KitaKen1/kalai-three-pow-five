import Kalai5.Endpoints.E20w.Certs1
import Kalai5.Endpoints.E20w.Certs2
import Kalai5.Endpoints.E20w.Certs3
import Kalai5.Endpoints.E20w.Certs4
import Kalai5.Endpoints.E20w.Certs5
import Kalai5.Endpoints.E20w.Certs6
import Kalai5.Endpoints.E20w.Certs7

/-! Exhaustive even-cell, local-stress, and parity coverage for (16,20). -/

namespace Kalai5.E20w

set_option maxHeartbeats 4000000

theorem cell_k1_g2s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k1_g2s0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht

theorem cell_k1_g2s2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.even_nF5
  rcases (show (C.nF5 : ℤ) ≤ 0 ∨ 2 ≤ (C.nF5 : ℤ) by omega) with b0 | b0
  · obtain ⟨q1, hq1⟩ := C.hD.even_r
    rcases (show (C.D.r : ℤ) ≤ 60 ∨ 62 ≤ (C.D.r : ℤ) by omega) with b1 | b1
    · exact leaf_k1_g2s2ll C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · exact leaf_k1_g2s2lr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
  · obtain ⟨q1, hq1⟩ := C.hD.even_r
    rcases (show (C.D.r : ℤ) ≤ 60 ∨ 62 ≤ (C.D.r : ℤ) by omega) with b1 | b1
    · exact leaf_k1_g2s2rl C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · exact leaf_k1_g2s2rr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht

theorem cell_k1_g2s4 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.hD.even_r
  rcases (show (C.D.r : ℤ) ≤ 60 ∨ 62 ≤ (C.D.r : ℤ) by omega) with b0 | b0
  · exact leaf_k1_g2s4l C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht
  · exact leaf_k1_g2s4r C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht

theorem cell_k1_g2s6 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.even_rS6
  rcases (show (C.rS6 : ℤ) ≤ 12 ∨ 14 ≤ (C.rS6 : ℤ) by omega) with b0 | b0
  · obtain ⟨q1, hq1⟩ := C.hD.even_x
    rcases (show (C.D.x : ℤ) ≤ 266 ∨ 268 ≤ (C.D.x : ℤ) by omega) with b1 | b1
    · exact leaf_k1_g2s6ll C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · exact leaf_k1_g2s6lr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
  · obtain ⟨q1, hq1⟩ := C.hD.even_x
    rcases (show (C.D.x : ℤ) ≤ 266 ∨ 268 ≤ (C.D.x : ℤ) by omega) with b1 | b1
    · exact leaf_k1_g2s6rl C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · exact leaf_k1_g2s6rr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht

theorem cell_k1_g2s8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k1_g2s8 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem closure1 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 18)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  by_cases hr0 : 12 ≤ C.D.G
  · exact leaf_k1_rect_g12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr1 : 12 ≤ C.D.Gs
  · exact leaf_k1_rect_s12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr2 : 10 ≤ C.D.Gs
  · exact leaf_k1_rect_s10 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr3 : C.D.G = 0
  · exact leaf_k1_rect_g0 C hJF hJS (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  by_cases hr4 : C.D.G = 4
  · exact leaf_k1_rect_g4 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr5 : C.D.G = 6
  · exact leaf_k1_rect_g6 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr6 : C.D.G = 8
  · exact leaf_k1_rect_g8 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr7 : C.D.G = 10
  · exact leaf_k1_rect_g10 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  rcases (show C.D.G = 2 by omega) with hGc
  · rcases (show C.D.Gs = 0 ∨ C.D.Gs = 2 ∨ C.D.Gs = 4 ∨ C.D.Gs = 6 ∨ C.D.Gs = 8 by omega) with hSc | hSc | hSc | hSc | hSc
    · exact cell_k1_g2s0 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k1_g2s2 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k1_g2s4 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k1_g2s6 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k1_g2s8 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht

theorem cell_k2_g0s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g0s0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht

theorem cell_k2_g0s2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g0s2 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht

theorem cell_k2_g0s4 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g0s4 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht

theorem cell_k2_g0s6 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g0s6 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht

theorem cell_k2_g0s8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g0s8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht

theorem cell_k2_g0s10 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 0)
    (hS : C.D.Gs = 10)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.hD.even_x
  rcases (show (C.D.x : ℤ) ≤ 266 ∨ 268 ≤ (C.D.x : ℤ) by omega) with b0 | b0
  · exact leaf_k2_g0s10l C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) b0 hc8 hs8 hql ht
  · exact leaf_k2_g0s10r C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) b0 hc8 hs8 hql ht

theorem cell_k2_g2s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g2s0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht

theorem cell_k2_g2s2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.hD.even_e
  rcases (show (C.D.e : ℤ) ≤ 56 ∨ 58 ≤ (C.D.e : ℤ) by omega) with b0 | b0
  · exact leaf_k2_g2s2l C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht
  · exact leaf_k2_g2s2r C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht

theorem cell_k2_g2s4 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.hD.even_x
  rcases (show (C.D.x : ℤ) ≤ 266 ∨ 268 ≤ (C.D.x : ℤ) by omega) with b0 | b0
  · exact leaf_k2_g2s4l C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht
  · exact leaf_k2_g2s4r C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht

theorem cell_k2_g2s6 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g2s6 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k2_g2s8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g2s8 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k2_g2s10 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 10)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g2s10 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k2_g6s0 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g6s0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht

theorem cell_k2_g6s2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g6s2 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k2_g6s4 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j3k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j3k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k2_g6s4_j3k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j2k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j2k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k2_g6s4_j2k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j1k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g6s4_j1k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k2_g6s4_j1k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g6s4_j0k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g6s4_j0k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_k2_g6s4_j0k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht

theorem cell_k2_g6s6 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.hD.even_y
  rcases (show (C.D.y : ℤ) ≤ 284 ∨ 286 ≤ (C.D.y : ℤ) by omega) with b0 | b0
  · exact leaf_k2_g6s6l C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht
  · obtain ⟨q1, hq1⟩ := C.hD.even_I
    rcases (show (C.D.I : ℤ) ≤ 136 ∨ 138 ≤ (C.D.I : ℤ) by omega) with b1 | b1
    · exact leaf_k2_g6s6rl C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · obtain ⟨q2, hq2⟩ := C.even_nF5
      rcases (show (C.nF5 : ℤ) ≤ 2 ∨ 4 ≤ (C.nF5 : ℤ) by omega) with b2 | b2
      · exact leaf_k2_g6s6rrl C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht
      · exact leaf_k2_g6s6rrr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht

theorem cell_k2_g6s8 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.even_nF5
  rcases (show (C.nF5 : ℤ) ≤ 2 ∨ 4 ≤ (C.nF5 : ℤ) by omega) with b0 | b0
  · exact leaf_k2_g6s8l C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht
  · exact leaf_k2_g6s8r C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 hc8 hs8 hql ht

theorem cell_k2_g6s10 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 10)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g6s10 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem closure2 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 40)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  by_cases hr0 : 12 ≤ C.D.G
  · exact leaf_k2_rect_g12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr1 : 12 ≤ C.D.Gs
  · exact leaf_k2_rect_s12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr2 : C.D.G = 4
  · exact leaf_k2_rect_g4 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr3 : C.D.G = 8
  · exact leaf_k2_rect_g8 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr4 : C.D.G = 10
  · exact leaf_k2_rect_g10 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  rcases (show C.D.G = 0 ∨ C.D.G = 2 ∨ C.D.G = 6 by omega) with hGc | hGc | hGc
  · rcases (show C.D.Gs = 0 ∨ C.D.Gs = 2 ∨ C.D.Gs = 4 ∨ C.D.Gs = 6 ∨ C.D.Gs = 8 ∨ C.D.Gs = 10 by omega) with hSc | hSc | hSc | hSc | hSc | hSc
    · exact cell_k2_g0s0 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g0s2 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g0s4 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g0s6 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g0s8 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g0s10 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
  · rcases (show C.D.Gs = 0 ∨ C.D.Gs = 2 ∨ C.D.Gs = 4 ∨ C.D.Gs = 6 ∨ C.D.Gs = 8 ∨ C.D.Gs = 10 by omega) with hSc | hSc | hSc | hSc | hSc | hSc
    · exact cell_k2_g2s0 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g2s2 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g2s4 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g2s6 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g2s8 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g2s10 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
  · rcases (show C.D.Gs = 0 ∨ C.D.Gs = 2 ∨ C.D.Gs = 4 ∨ C.D.Gs = 6 ∨ C.D.Gs = 8 ∨ C.D.Gs = 10 by omega) with hSc | hSc | hSc | hSc | hSc | hSc
    · exact cell_k2_g6s0 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g6s2 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g6s4 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g6s6 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g6s8 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht
    · exact cell_k2_g6s10 C hJF hJS hpairF hpairS hGc hSc hc8 hs8 hql ht

theorem closure3 (C : Ctx 16 20 8 10 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 66)
    (hql : ((C.F.rows.map q55RowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  by_cases hr0 : 12 ≤ C.D.G
  · exact leaf_k3_rect_g12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr1 : 12 ≤ C.D.Gs
  · exact leaf_k3_rect_s12 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr2 : 10 ≤ C.D.Gs
  · exact leaf_k3_rect_s10 C hJF hJS (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr3 : C.D.G = 0
  · exact leaf_k3_rect_g0 C hJF hJS (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  by_cases hr4 : C.D.G = 2
  · exact leaf_k3_rect_g2 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr5 : C.D.G = 4
  · exact leaf_k3_rect_g4 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr6 : C.D.G = 6
  · exact leaf_k3_rect_g6 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr7 : C.D.G = 8
  · exact leaf_k3_rect_g8 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  by_cases hr8 : C.D.G = 10
  · exact leaf_k3_rect_g10 C hJF hJS (by omega) (by omega) (by omega) hc8 hs8 hql ht
  omega

end Kalai5.E20w
