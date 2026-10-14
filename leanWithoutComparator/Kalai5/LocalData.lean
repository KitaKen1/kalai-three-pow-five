import Kalai5.FlagData

/-!
# Facet rows and summed local identities

Each facet `F` of a 5-polytope is a 4-polytope with combinatorial row `(n, e, p, r; J)`
(`J = f₀₃(F)`).  Summing over all facets gives the local-to-global identities

`Σ n = f₀₄`, `Σ e = f₁₄`, `Σ p = f₂₄`, `Σ r = 2 f₃`, `Σ J = 2 f₀₃`,

which turn local inequalities (`L1`, `L2`, `L3`, local `g ≥ 0`) into global bounds on `t`.
-/

namespace Kalai5

/-- Combinatorial row `(n, e, p, r; J)` of a 4-dimensional facet, `J = f₀₃`. -/
structure Row where
  n : ℕ
  e : ℕ
  p : ℕ
  r : ℕ
  J : ℕ
  deriving DecidableEq, Repr

namespace Row

/-- Local toric `g₂ = J - 3n - 3r + 10`. -/
def g (R : Row) : ℤ := R.J - 3 * R.n - 3 * R.r + 10

/-- `L1 = 9p - 5e - n - J - 15` (MAIN_PROOF §5, endpoint (14,26)). -/
def L1 (R : Row) : ℤ := 9 * R.p - 5 * R.e - R.n - R.J - 15

/-- `L2 = 12n - 10e + 12p - 3J - 20 + 5[n = 7]` (endpoint (14,24)). -/
def L2 (R : Row) : ℤ := 12 * R.n - 10 * R.e + 12 * R.p - 3 * R.J - 20 + if R.n = 7 then 5 else 0

/-- `L3 = 16n + 2p + 31r - 10J - 48 + 12[n = 7]` (endpoint (14,20)). -/
def L3 (R : Row) : ℤ := 16 * R.n + 2 * R.p + 31 * R.r - 10 * R.J - 48 + if R.n = 7 then 12 else 0

end Row

/-- The rows of all facets of a polytope with flag data `D`, with the summed identities. -/
structure FacetRows (D : FlagData) where
  rows : List Row
  length_eq : rows.length = D.h
  sum_n : (rows.map Row.n).sum = D.I
  sum_e : (rows.map Row.e).sum = D.f14
  sum_p : (rows.map Row.p).sum = D.y
  sum_r : (rows.map Row.r).sum = 2 * D.r
  sum_J : (rows.map Row.J).sum = 2 * D.f03

/-- Sums of linear functions of the rows. -/
lemma sum_map_linear (rows : List Row) (cn ce cp cr cJ c0 : ℤ) :
    (rows.map fun R => cn * R.n + ce * R.e + cp * R.p + cr * R.r + cJ * R.J + c0).sum =
      cn * ((rows.map Row.n).sum : ℕ) + ce * ((rows.map Row.e).sum : ℕ)
        + cp * ((rows.map Row.p).sum : ℕ) + cr * ((rows.map Row.r).sum : ℕ)
        + cJ * ((rows.map Row.J).sum : ℕ) + c0 * rows.length := by
  induction rows with
  | nil => simp
  | cons R rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast; ring

/-- Sum of an indicator over the rows. -/
lemma sum_map_ite (rows : List Row) (P : Row → Prop) [DecidablePred P] (c : ℤ) :
    (rows.map fun R => if P R then c else 0).sum = c * (rows.filter fun R => P R).length := by
  induction rows with
  | nil => simp
  | cons R rs ih =>
    by_cases h : P R <;> simp [List.filter_cons, h, ih] <;> ring

namespace FacetRows

variable {D : FlagData} (F : FacetRows D)

lemma sum_g (hD : D.Valid) :
    (F.rows.map Row.g).sum = 2 * D.G + 4 * D.v + 4 * D.h - D.I - 8 := by
  have h := sum_map_linear F.rows (-3) 0 0 (-3) 1 10
  have hfun : (fun R : Row => (-3 : ℤ) * R.n + 0 * R.e + 0 * R.p + (-3) * R.r + 1 * R.J + 10)
      = Row.g := by funext R; simp only [Row.g]; ring
  rw [hfun, F.sum_n, F.sum_r, F.sum_J, F.length_eq] at h
  rw [h]; have := hD.euler; have := hD.f03_eq
  simp only [FlagData.G]; push_cast; linarith

lemma sum_L1 (hD : D.Valid) :
    12 * (D.t : ℤ) = 48 * D.v + 33 * D.h - 96 + 4 * D.A + 6 * D.G + (F.rows.map Row.L1).sum := by
  have h := sum_map_linear F.rows (-1) (-5) 9 0 (-1) (-15)
  have hfun : (fun R : Row => (-1 : ℤ) * R.n + (-5) * R.e + 9 * R.p + 0 * R.r + (-1) * R.J + (-15))
      = Row.L1 := by funext R; simp only [Row.L1]; ring
  rw [hfun, F.sum_n, F.sum_e, F.sum_p, F.sum_J, F.length_eq] at h
  rw [h]; have := hD.euler; have := hD.f03_eq; have := hD.f14_eq; have := hD.f024_eq
  simp only [FlagData.A, FlagData.G, FlagData.t]; push_cast; linarith

lemma sum_L2 (hD : D.Valid) :
    6 * (D.t : ℤ) = 34 * D.v + 14 * D.h - 68
      - 5 * (F.rows.filter fun R => R.n = 7).length
      + 2 * D.A + 8 * D.G + (F.rows.map Row.L2).sum := by
  have h := sum_map_linear F.rows 12 (-10) 12 0 (-3) (-20)
  have hi := sum_map_ite F.rows (fun R => R.n = 7) 5
  have hfun : (F.rows.map Row.L2).sum =
      (F.rows.map fun R : Row => (12 : ℤ) * R.n + (-10) * R.e + 12 * R.p + 0 * R.r
        + (-3) * R.J + (-20)).sum + (F.rows.map fun R : Row => if R.n = 7 then (5 : ℤ) else 0).sum := by
    rw [← List.sum_map_add]; congr 1; apply List.map_congr_left; intro R _; simp only [Row.L2]; ring
  rw [hfun, h, hi, F.sum_n, F.sum_e, F.sum_p, F.sum_J, F.length_eq]
  have := hD.euler; have := hD.f03_eq; have := hD.f14_eq; have := hD.f024_eq
  simp only [FlagData.A, FlagData.G, FlagData.t]; push_cast; linarith

lemma sum_L3 (hD : D.Valid) :
    (F.rows.map Row.L3).sum + 2 * D.A + 22 * D.G
      = 6 * (D.t : ℤ) - 62 * D.v + 124 + 12 * (F.rows.filter fun R => R.n = 7).length := by
  have h := sum_map_linear F.rows 16 0 2 31 (-10) (-48)
  have hi := sum_map_ite F.rows (fun R => R.n = 7) 12
  have hfun : (F.rows.map Row.L3).sum =
      (F.rows.map fun R : Row => (16 : ℤ) * R.n + 0 * R.e + 2 * R.p + 31 * R.r
        + (-10) * R.J + (-48)).sum + (F.rows.map fun R : Row => if R.n = 7 then (12 : ℤ) else 0).sum := by
    rw [← List.sum_map_add]; congr 1; apply List.map_congr_left; intro R _; simp only [Row.L3]; ring
  rw [hfun, h, hi, F.sum_n, F.sum_p, F.sum_r, F.sum_J, F.length_eq]
  have := hD.euler; have := hD.f03_eq; have := hD.f14_eq; have := hD.f024_eq
  simp only [FlagData.A, FlagData.G, FlagData.t]; push_cast; linarith

end FacetRows

end Kalai5
