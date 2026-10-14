import Kalai5.Endpoints.Fourteen
import Kalai5.Catalog.Small
import Kalai5.Rows.Degree
import Kalai5.Rows.Dual

/-!
# Endpoint `(16,24)`

`12 t = 1464 + 4A + 6G + Σ_F L1(F)` at `(16,24)` (`sum_L1`), and `L1 ≥ 0` on every facet row
except the row `tRow = (8,16,14,6; 32)` of the prism over a tetrahedron:

* `n ≤ 7`: the rows of `smallRows`;
* `n = 8`, `r ≤ 7`: the dual row lies in `smallRows` (`realRow_dual`), and the four duals with
  eight vertices have `L1 = -9, 5, 4, 9` (the `-9` is `tRow`);
* `n = 8`, `r ≥ 8`: `L1 ≥ 9 r - 63` by Euler and `J + 4n ≤ 4e` (`realRow_B4`).

A facet with row `tRow` is handled by the obligation `full_prism_16`.
-/

namespace Kalai5

/-- Row of the prism over a tetrahedron. -/
def tRow : Row := ⟨8, 16, 14, 6, 32⟩

/-- The dual row `(r, p, e, n; J)`. -/
def Row.dual (R : Row) : Row := ⟨R.r, R.p, R.e, R.n, R.J⟩

/-- The duals of the small rows with eight facets: `L1 ≥ 0` except for `tRow`. -/
lemma smallRows_dual_L1 : ∀ R ∈ smallRows, R.r = 8 → R.dual ≠ tRow → 0 ≤ R.dual.L1 := by
  decide +kernel

/-- **`L1 ≥ 0` on rows of 4-polytopes with at most eight vertices, except `tRow`.** -/
lemma L1_nonneg_of_le_eight (hcls : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows) {R : Row}
    (hR : IsRealRow R) (h8 : R.n ≤ 8) (hT : R ≠ tRow) : 0 ≤ R.L1 := by
  rcases Nat.lt_or_ge R.n 8 with h7 | h8'
  · exact smallRows_L1 R (hcls R hR (by omega))
  · have hn : R.n = 8 := by omega
    rcases Nat.lt_or_ge R.r 8 with hr | hr
    · -- the dual row is small
      have hd := realRow_dual hR
      have hmem := hcls _ hd (show R.r ≤ 7 by omega)
      have hdd : (⟨R.r, R.p, R.e, R.n, R.J⟩ : Row).dual = R := rfl
      have := smallRows_dual_L1 _ hmem (by simp [hn]) (by rw [hdd]; exact hT)
      rwa [hdd] at this
    · -- many facets: Euler and `J + 4n ≤ 4e`
      have he := realRow_euler hR
      have hb := realRow_B4 hR
      simp only [Row.L1]
      omega

/-- **Endpoint (16,24)**: `L1 ≥ 0` on all facets closes the case. -/
theorem closure_16_24 {D : FlagData} (hD : D.Valid) (F : FacetRows D) (hv : D.v = 16)
    (hh : D.h = 24) (hL1 : ∀ R ∈ F.rows, 0 ≤ R.L1) : 243 ≤ D.total := by
  have hsum := F.sum_L1 hD
  have hpos := sum_nonneg_of_rows hL1
  have hA := hD.A_nonneg; have hG := hD.G_nonneg
  rw [hv, hh] at hsum
  apply FlagData.total_ge_of_t_gt hD
  have : (1464 : ℤ) ≤ 12 * D.t := by push_cast at hsum; linarith
  omega

end Kalai5
