import Kalai5.Endpoints.E18q.Certs1
import Kalai5.Endpoints.E18q.Certs2
import Kalai5.Endpoints.E18q.Certs3
import Kalai5.Endpoints.E18q.Certs4
import Kalai5.Endpoints.E18q.Certs5
import Kalai5.Endpoints.E18q.Certs6
import Kalai5.Endpoints.E18q.Certs7
import Kalai5.Endpoints.E18q.Certs8
import Kalai5.Endpoints.E18q.Certs9

/-! Complete parity/stress coverage of the listed cells, not the whole endpoint. -/
namespace Kalai5.E18q
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

theorem cell_k2_g2s12 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 2)
    (hS : C.D.Gs = 12)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k2_g2s12 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k2_g4s8 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 4)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 4)
    (hs8 : sumR8 C.F.rows ≤ 36)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j2k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j2k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j2k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j2k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k2_g4s8_j2k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j1k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j1k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j1k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k2_g4s8_j1k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k2_g4s8_j1k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nF : cntBig C.F.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g4s8_j0k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
      have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g4s8_j0k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
      have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g4s8_j0k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k2_g4s8_j0k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_k2_g4s8_j0k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht

theorem cell_k3_g6s12 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 6)
    (hS : C.D.Gs = 12)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 6 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 12 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (6 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 6 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (5 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 5 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
        have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
        have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 8 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 10 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j3k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g6s12_j3k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (6 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 6 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (5 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 5 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
        have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
        have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 8 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 10 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j2k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g6s12_j2k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (6 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 6 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (5 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 5 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
        have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
        have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 8 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 10 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g6s12_j1k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g6s12_j1k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nF : cntBig C.F.rows 6 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  rcases rows_split_max C.Fs.rows (6 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 6 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k6 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (5 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
      have := hpairS 5 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k5 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (4 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 4 ≤ 2 := by
      have := hpairS 4 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k4 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (3 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 6 ≤ 2 := by
      have := hpairS 3 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k3 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 8 ≤ 2 := by
      have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 10 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g6s12_j0k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 12 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_k3_g6s12_j0k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht

theorem cell_k3_g8s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 8)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 8 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 4 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j4k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j4k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g8s4_j4k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j3k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j3k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g8s4_j3k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j2k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j2k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g8s4_j2k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j1k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g8s4_j1k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g8s4_j1k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nF : cntBig C.F.rows 8 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  rcases rows_split_max C.Fs.rows (2 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 2 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g8s4_j0k2 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 2 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g8s4_j0k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 4 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_k3_g8s4_j0k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht

theorem cell_k3_g16s0 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 0)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s0 C hJF hJS (by omega) (by omega) (by omega) (by omega) (C.polyFs (by omega)) hc8 hs8 hql ht

theorem cell_k3_g16s2 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 2)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  have cF : ∀ R ∈ C.F.rows, 2 * R.g ≤ 16 := fun R hR => by
    have := (C.rowF R hR).g_le; omega
  have cS : ∀ R ∈ C.Fs.rows, 2 * R.g ≤ 2 := fun R hR => by
    have := (C.rowFs R hR).g_le; omega
  rcases rows_split_max C.F.rows (8 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 0 ≤ 2 := by
      have := hpairF 8 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j8k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j8k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (7 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 2 ≤ 2 := by
      have := hpairF 7 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j7k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j7k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (6 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 4 ≤ 2 := by
      have := hpairF 6 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j6k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j6k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (5 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 6 ≤ 2 := by
      have := hpairF 5 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j5k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j5k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (4 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 8 ≤ 2 := by
      have := hpairF 4 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j4k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j4k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (3 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 10 ≤ 2 := by
      have := hpairF 3 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j3k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j3k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (2 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 12 ≤ 2 := by
      have := hpairF 2 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j2k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j2k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  rcases rows_split_max C.F.rows (1 : ℤ) with mF | cF
  · have nF : cntBig C.F.rows 14 ≤ 2 := by
      have := hpairF 1 mF; rw [hG] at this; norm_num at this; exact this
    rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
    · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
        have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
      exact leaf_k3_g16s2_j1k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
    have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
      have := cS R hR; omega
    exact leaf_k3_g16s2_j1k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nF : cntBig C.F.rows 16 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cF R hR; omega
  rcases rows_split_max C.Fs.rows (1 : ℤ) with mS | cS
  · have nS : cntBig C.Fs.rows 0 ≤ 2 := by
      have := hpairS 1 mS; rw [hS] at this; norm_num at this; exact this
    exact leaf_k3_g16s2_j0k1 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht
  have nS : cntBig C.Fs.rows 2 ≤ 2 := cntBig_le_of_cap fun R hR => by
    have := cS R hR; omega
  exact leaf_k3_g16s2_j0k0 C hJF hJS (by omega) (by omega) (by omega) (by omega) cF nF cS nS hc8 hs8 hql ht

theorem cell_k3_g16s4 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 4)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s4 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k3_g16s6 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 6)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s6 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k3_g16s8 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 8)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s8 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k3_g16s10 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 10)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s10 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k3_g16s12 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 12)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s12 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

theorem cell_k3_g16s14 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hpairF : ∀ j : ℤ, (∃ R ∈ C.F.rows, j ≤ R.g) → cntBig C.F.rows (C.D.G - 2 * j) ≤ 2)
    (hpairS : ∀ j : ℤ, (∃ R ∈ C.Fs.rows, j ≤ R.g) → cntBig C.Fs.rows (C.D.Gs - 2 * j) ≤ 2)
    (hG : C.D.G = 16)
    (hS : C.D.Gs = 14)
    (hc8 : cnt8 C.F.rows = 6)
    (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55StrongRowWeight).sum : ℤ) ≤ 4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  exact leaf_k3_g16s14 C hJF hJS (by omega) (by omega) (by omega) (by omega) hc8 hs8 hql ht

end Kalai5.E18q
