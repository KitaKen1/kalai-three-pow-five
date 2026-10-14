import Kalai5.Endpoints.Fourteen
import Kalai5.Catalog.Small

/-!
# Endpoint `(14,22)` without stress localization

`M22 = L2 - 5[n = 7] = 12n - 10e + 12p - 3J - 20` satisfies
`6t = 34v + 14h - 68 + 2A + 8G + Σ_F M22(F)` (from `sum_L2`), and `M22 ≥ 0` on every small row
except `excRow` (`M22(excRow) = -5`).  At `(14,22)` this gives `t ≥ 358/3`, so `t ≥ 120`, using
only `G, A ≥ 0`, the classification of the rows, and the absence of `excRow`
(design note `phase2_14.md` §3.2).
-/

namespace Kalai5

/-- `L2` without the bonus for seven-vertex facets. -/
def Row.M22 (R : Row) : ℤ := 12 * R.n - 10 * R.e + 12 * R.p - 3 * R.J - 20

lemma smallRows_M22 : ∀ R ∈ smallRows, R ≠ excRow → 0 ≤ R.M22 := by decide +kernel

lemma Row.L2_eq_M22 (R : Row) : R.L2 = R.M22 + if R.n = 7 then 5 else 0 := by
  simp only [Row.L2, Row.M22]

namespace FacetRows

variable {D : FlagData} (F : FacetRows D)

lemma sum_M22 (hD : D.Valid) :
    6 * (D.t : ℤ) = 34 * D.v + 14 * D.h - 68 + 2 * D.A + 8 * D.G + (F.rows.map Row.M22).sum := by
  have h := F.sum_L2 hD
  have hi := sum_map_ite F.rows (fun R => R.n = 7) 5
  have hL : (F.rows.map Row.L2).sum =
      (F.rows.map Row.M22).sum + (F.rows.map fun R => if R.n = 7 then (5 : ℤ) else 0).sum := by
    rw [← List.sum_map_add]
    exact congrArg List.sum (List.map_congr_left fun R _ => Row.L2_eq_M22 R)
  rw [hL, hi] at h
  linarith

end FacetRows

/-- **Endpoint (14,22)** from `M22 ≥ 0` on all facets. -/
theorem closure_14_22_M22 {D : FlagData} (hD : D.Valid) (F : FacetRows D) (hv : D.v = 14)
    (hh : D.h = 22) (hM : ∀ R ∈ F.rows, 0 ≤ R.M22) : 243 ≤ D.total := by
  have hsum := F.sum_M22 hD
  have hpos := sum_nonneg_of_rows hM
  have hA := hD.A_nonneg; have hG := hD.G_nonneg
  rw [hv, hh] at hsum
  apply FlagData.total_ge_of_t_gt hD
  have : (716 : ℤ) ≤ 6 * D.t := by push_cast at hsum; linarith
  omega

end Kalai5
