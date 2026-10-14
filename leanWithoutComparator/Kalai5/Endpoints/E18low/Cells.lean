import Kalai5.Endpoints.E18low.Certs1
import Kalai5.Endpoints.E18low.Certs2
import Kalai5.Endpoints.E18low.Certs3
import Kalai5.Endpoints.E18low.Certs4
import Kalai5.Endpoints.E18low.Certs5
import Kalai5.Endpoints.E18low.Certs6
import Kalai5.Endpoints.E18low.Certs7
import Kalai5.Endpoints.E18low.Certs8
import Kalai5.Endpoints.E18low.Certs9
import Kalai5.Endpoints.E18low.Certs10
import Kalai5.Endpoints.E18low.Certs11
import Kalai5.Endpoints.E18low.Certs12
import Kalai5.Endpoints.E18low.Certs13
import Kalai5.Endpoints.E18low.Certs14
import Kalai5.Endpoints.E18low.Certs15
import Kalai5.Endpoints.E18low.Certs16
import Kalai5.Endpoints.E18low.Certs17
import Kalai5.Endpoints.E18low.Certs18
import Kalai5.Endpoints.E18low.Certs19

namespace Kalai5.E18low
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

theorem cell_k1_g4s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 4)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.even_rS6
  rcases (show (C.rS6 : ℤ) ≤ 10 ∨ 12 ≤ (C.rS6 : ℤ) by omega) with b0 | b0
  · obtain ⟨q1, hq1⟩ := C.hD.even_e
    rcases (show (C.D.e : ℤ) ≤ 56 ∨ 58 ≤ (C.D.e : ℤ) by omega) with b1 | b1
    · exact leaf_low_k1_g4s6ll C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
    · exact leaf_low_k1_g4s6lr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 hc8 hs8 hql ht
  · obtain ⟨q1, hq1⟩ := C.even_rS5
    rcases (show (C.rS5 : ℤ) ≤ 0 ∨ 2 ≤ (C.rS5 : ℤ) by omega) with b1 | b1
    · obtain ⟨q2, hq2⟩ := C.hD.even_e
      rcases (show (C.D.e : ℤ) ≤ 56 ∨ 58 ≤ (C.D.e : ℤ) by omega) with b2 | b2
      · exact leaf_low_k1_g4s6rll C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht
      · exact leaf_low_k1_g4s6rlr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht
    · obtain ⟨q2, hq2⟩ := C.hD.even_e
      rcases (show (C.D.e : ℤ) ≤ 56 ∨ 58 ≤ (C.D.e : ℤ) by omega) with b2 | b2
      · exact leaf_low_k1_g4s6rrl C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht
      · exact leaf_low_k1_g4s6rrr C hJF hJS (by omega) (by omega) (by omega) (by omega) b0 b1 b2 hc8 hs8 hql ht

theorem cell_k1_g2s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k1_g2s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k1_g2s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k1_g2s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k1_g2s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k1_g2s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k1_g2s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k1_g2s6_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k1_g2s6_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k1_g4s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 4)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_low_k1_g4s2_S1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_low_k1_g4s2_S0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cS nS hc8 hs8 hql ht

theorem cell_k1_g4s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 4)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 2)
    (hs8 : sumR8 C.F.rows ≤ 16)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k1_g4s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k1_g4s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k1_g4s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g4s10 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 4)
    (hS : C.D.Gs = 10)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g4s10_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g4s10_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g4s10_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g6s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g6s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g6s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g6s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g6s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s6_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s6_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s6_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g6s6_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g6s8 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s8_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s8_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g6s8_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g6s8_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g8s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 8)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g8s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g8s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 8)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s4_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g8s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g8s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 8)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s6_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s6_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s6_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g8s6_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g8s6_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g10s0 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s0_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s0_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s0_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s0_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s0_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g10s0_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht

theorem cell_k2_g10s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s2_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g10s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g10s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s4_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s4_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g10s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g10s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k2_g12s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 12)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 12 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k2_g12s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k2_g12s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g8s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 8)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g8s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g8s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g8s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g8s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g8s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g10s0 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 0 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s0_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s0_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s0_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s0_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s0_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g10s0_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) cF nF hc8 hs8 hql ht

theorem cell_k3_g10s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s2_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g10s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g10s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s4_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s4_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g10s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g10s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s6_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s6_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s6_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s6_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s6_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g10s6_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g10s8 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 10)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 10 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s8_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s8_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s8_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s8_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g10s8_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 10 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g10s8_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g12s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 12)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 12 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g12s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g12s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 12)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 12 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g12s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g12s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 12)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 12 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g12s6_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g12s6_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g14s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 14)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 14 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (7 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 7 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F7 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 12 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s2_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 14 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g14s2_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

theorem cell_k3_g14s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 14)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 14 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (7 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 7 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F7 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 12 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    exact leaf_low_k3_g14s4_F1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht
  have nF : cntBig C.F.rows 14 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  exact leaf_low_k3_g14s4_F0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF hc8 hs8 hql ht

end Kalai5.E18low
