import Kalai5.Endpoints.E18low.Cells
import Kalai5.Endpoints.E18q.Cells

namespace Kalai5.E18low
set_option maxHeartbeats 12000000

/-- Explicit residual cells; membership is a necessary condition for a counterexample. -/
def remainingCells : ℕ → List (ℤ × ℤ)
  | 1 => [(0, 10)]
  | 2 => [(0, 10), (2, 2), (2, 4), (2, 6), (2, 8), (2, 10), (4, 2), (4, 4), (4, 6)]
  | 3 => [(0, 10), (2, 2), (2, 4), (2, 6), (2, 8), (2, 10), (2, 12), (2, 14), (4, 2), (4, 4), (4, 6), (4, 8), (4, 10), (4, 12), (4, 14), (6, 2), (6, 4), (6, 6), (6, 8), (6, 10), (8, 6), (8, 8), (8, 10)]
  | _ => []

theorem reduction1 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118)
    (hG14 : C.D.G ≤ 14) (hS14 : C.D.Gs ≤ 14) :
    (C.D.G, C.D.Gs) ∈ remainingCells 1 := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  have hg0 : 0 ≤ g := by omega
  have hg7 : g ≤ 7 := by omega
  have hs0 : 0 ≤ s := by omega
  have hs7 : s ≤ 7 := by omega
  interval_cases g <;> interval_cases s
  · exfalso
    exact leaf_low_rect_k1_g0_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k1_g0_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g2s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g2s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g2s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_2s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g4s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g4s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k1_g4s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g4_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g2_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_6s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_6s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g0_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g8_10s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g8_10s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g10_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k1_g6_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem reduction2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118)
    (hG14 : C.D.G ≤ 14) (hS14 : C.D.Gs ≤ 14) :
    (C.D.G, C.D.Gs) ∈ remainingCells 2 := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  have hg0 : 0 ≤ g := by omega
  have hg7 : g ≤ 7 := by omega
  have hs0 : 0 ≤ s := by omega
  have hs7 : s ≤ 7 := by omega
  interval_cases g <;> interval_cases s
  · exfalso
    exact leaf_low_rect_k2_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k2_g0_0s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_14s14_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k2_g2_2s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_14s14_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact E18q.cell_k2_g4s8 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g4s10 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g4_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g4_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g6s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g6s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g6s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g6s8 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g6_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g4_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g4_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g8s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g8s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g8s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g10s0 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g10s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g10s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g10_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g12_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k2_g12s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g12_14s4_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g12_14s4_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g14_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g14_14s0_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g12_14s4_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g12_14s4_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k2_g8_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem reduction3 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118)
    (hG14 : C.D.G ≤ 14) (hS14 : C.D.Gs ≤ 14) :
    (C.D.G, C.D.Gs) ∈ remainingCells 3 := by
  have hG0 := C.hD.G_nonneg; have hS0 := C.hD.Gs_nonneg
  obtain ⟨g, hg⟩ := FlagData.even_G C.hD
  obtain ⟨s, hs⟩ := C.even_Gs
  have hg0 : 0 ≤ g := by omega
  have hg7 : g ≤ 7 := by omega
  have hs0 : 0 ≤ s := by omega
  have hs7 : s ≤ 7 := by omega
  interval_cases g <;> interval_cases s
  · exfalso
    exact leaf_low_rect_k3_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_0s0_8 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k3_g0_0s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_0s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyF (by omega)) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k3_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k3_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact E18q.cell_k3_g6s12 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g6_14s14_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g0_8s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g8s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact E18q.cell_k3_g8s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · norm_num [remainingCells, hg, hs]
  · exfalso
    exact leaf_low_rect_k3_g8_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g8_14s12_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g10s0 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g10s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g10s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g10s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g10s8 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g12_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g12s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g12s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g12s6 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g12_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g12_14s0_0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g14s2 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact cell_k3_g14s4 C hJF hJS hpairF hpairS (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g14_14s6_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g12_14s8_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht
  · exfalso
    exact leaf_low_rect_k3_g10_14s10_14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

end Kalai5.E18low
