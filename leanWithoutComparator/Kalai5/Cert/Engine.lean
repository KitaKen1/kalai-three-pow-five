import Kalai5.Endpoints.Sixteen
import Kalai5.Rows.Box

/-!
# A certificate engine for the endpoint counting

A *local cost* `φ : Cost` is an affine function of a row `(n, e, p, r; J)` plus indicator terms
`[n = 5]`, `[n = 6]`, `[r = 5]`, `[r = 6]`.  Over a list of facet rows with the summed identities,
`Σ φ(R)` is a linear expression in the flag numbers and four counts (`Cost.sum_eval`).  If `φ ≥ 0`
on every admissible row, `0 ≤ Σ φ(R)` is a linear inequality on the flag numbers; such inequalities
for the facets of `P` and of its polar close the endpoint cases by `linarith`.

Admissible rows (`RowOK`): Euler, `J + 4n ≤ 4e` and its dual, `2e ≤ n (n - 1)`, `0 ≤ g`,
`2g ≤ Gcap`, `n ≤ nmax`, not in an exclusion list, and in `smallRows` (resp. its duals) when
`n ≤ 7` (resp. `r ≤ 7`).  Nonnegativity of a cost is checked by `decide` on the small rows
(`Cost.checkSmall`) and by `omega` on the box `n, r ≥ 8`.
-/

namespace Kalai5

lemma Row.dual_dual (R : Row) : R.dual.dual = R := by cases R; rfl

/-- The facts the certificate engine uses about an admissible facet row. -/
structure RowOK (nmax : ℕ) (Gcap : ℤ) (excl : List Row) (R : Row) : Prop where
  n_le : R.n ≤ nmax
  g_nonneg : 0 ≤ R.g
  g_le : 2 * R.g ≤ Gcap
  euler : (R.n : ℤ) - R.e + R.p - R.r = 0
  B4 : R.J + 4 * R.n ≤ 4 * R.e
  B4d : R.J + 4 * R.r ≤ 4 * R.p
  ube : 2 * R.e ≤ R.n * (R.n - 1)
  small : R.n ≤ 7 → R ∈ smallRows
  smalld : R.r ≤ 7 → R.dual ∈ smallRows
  notex : R ∉ excl

lemma RowOK.mono {nmax : ℕ} {G G' : ℤ} {excl : List Row} {R : Row} (h : RowOK nmax G excl R)
    (hG : G ≤ G') : RowOK nmax G' excl R :=
  { h with g_le := le_trans h.g_le hG }

/-- Rows with at most eleven vertices have `2g ≤ 1000` (from `2e ≤ n (n - 1)` and `J + 4n ≤ 4e`). -/
lemma RowOK.capped {nmax : ℕ} {G : ℤ} {excl : List Row} {R : Row} (h : RowOK nmax G excl R)
    (hn : nmax ≤ 11) : RowOK nmax 1000 excl R := by
  refine { h with g_le := ?_ }
  have h1 := h.ube
  have h2 := h.B4
  have h3 : R.n ≤ 11 := le_trans h.n_le hn
  have h4 : R.n * (R.n - 1) ≤ 110 := by
    have : R.n - 1 ≤ 10 := by omega
    calc R.n * (R.n - 1) ≤ 11 * 10 := Nat.mul_le_mul h3 this
      _ = 110 := by norm_num
  simp only [Row.g]
  omega

/-- A real row satisfies all row facts except the bounds, given the classification. -/
lemma rowOK_of_real (hcls : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows) {R : Row}
    (hR : IsRealRow R) {nmax : ℕ} {Gcap : ℤ} {excl : List Row} (hn : R.n ≤ nmax) (hg : 0 ≤ R.g)
    (hgG : 2 * R.g ≤ Gcap) (hex : R ∉ excl) : RowOK nmax Gcap excl R where
  n_le := hn
  g_nonneg := hg
  g_le := hgG
  euler := realRow_euler hR
  B4 := realRow_B4 hR
  B4d := realRow_B4 (realRow_dual hR)
  ube := realRow_ube hR
  small := hcls R hR
  smalld := fun h => hcls _ (realRow_dual hR) h
  notex := hex

/-- A local cost: affine in the row, plus indicators of `n ∈ {5, 6}` and `r ∈ {5, 6}`. -/
structure Cost where
  c0 : ℤ
  cn : ℤ
  ce : ℤ
  cp : ℤ
  cr : ℤ
  cJ : ℤ
  a5 : ℤ
  a6 : ℤ
  b5 : ℤ
  b6 : ℤ

namespace Cost

/-- The affine part. -/
def aff (φ : Cost) (R : Row) : ℤ :=
  φ.c0 + φ.cn * R.n + φ.ce * R.e + φ.cp * R.p + φ.cr * R.r + φ.cJ * R.J

/-- The cost of a row. -/
def eval (φ : Cost) (R : Row) : ℤ :=
  φ.aff R + (if R.n = 5 then φ.a5 else 0) + (if R.n = 6 then φ.a6 else 0) +
    (if R.r = 5 then φ.b5 else 0) + (if R.r = 6 then φ.b6 else 0)

lemma eval_of_ge {φ : Cost} {R : Row} (hn : 8 ≤ R.n) (hr : 8 ≤ R.r) : φ.eval R = φ.aff R := by
  simp [eval, show R.n ≠ 5 by omega, show R.n ≠ 6 by omega, show R.r ≠ 5 by omega,
    show R.r ≠ 6 by omega]

/-- Number of rows with `n = k`. -/
def cntN (rows : List Row) (k : ℕ) : ℕ := (rows.filter fun R => R.n = k).length

/-- Number of rows with `r = k`. -/
def cntR (rows : List Row) (k : ℕ) : ℕ := (rows.filter fun R => R.r = k).length

/-- **The summed cost** is linear in the row sums and the four counts. -/
lemma sum_eval (φ : Cost) (rows : List Row) :
    (rows.map φ.eval).sum = φ.c0 * rows.length + φ.cn * ((rows.map Row.n).sum : ℕ)
      + φ.ce * ((rows.map Row.e).sum : ℕ) + φ.cp * ((rows.map Row.p).sum : ℕ)
      + φ.cr * ((rows.map Row.r).sum : ℕ) + φ.cJ * ((rows.map Row.J).sum : ℕ)
      + φ.a5 * (cntN rows 5 : ℕ) + φ.a6 * (cntN rows 6 : ℕ) + φ.b5 * (cntR rows 5 : ℕ)
      + φ.b6 * (cntR rows 6 : ℕ) := by
  induction rows with
  | nil => simp [cntN, cntR]
  | cons R rs ih =>
    simp only [cntN, cntR] at ih
    simp only [List.map_cons, List.sum_cons, List.length_cons, cntN, cntR, List.filter_cons, ih]
    simp only [eval, aff]
    by_cases h5 : R.n = 5 <;> by_cases h6 : R.n = 6 <;> by_cases k5 : R.r = 5 <;>
      by_cases k6 : R.r = 6 <;> simp [h5, h6, k5, k6] <;> push_cast <;> ring

/-- Small rows of 4-polytopes and their duals. -/
def smallAll : List Row := smallRows ++ smallRows.map Row.dual

/-- The cost is nonnegative on the admissible small rows. -/
def checkSmall (φ : Cost) (nmax : ℕ) (Gcap : ℤ) (excl : List Row) : Bool :=
  smallAll.all fun R => decide (R.n ≤ nmax → 2 * R.g ≤ Gcap → R ∉ excl → 0 ≤ φ.eval R)

lemma nonneg_of_checkSmall {φ : Cost} {nmax : ℕ} {Gcap : ℤ} {excl : List Row}
    (hc : φ.checkSmall nmax Gcap excl = true) {R : Row} (hR : RowOK nmax Gcap excl R)
    (h7 : R.n ≤ 7 ∨ R.r ≤ 7) : 0 ≤ φ.eval R := by
  have hmem : R ∈ smallAll := by
    rcases h7 with h | h
    · exact List.mem_append_left _ (hR.small h)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨R.dual, hR.smalld h, Row.dual_dual R⟩)
  have := List.all_eq_true.1 hc R hmem
  exact (of_decide_eq_true this) hR.n_le hR.g_le hR.notex

/-- **Nonnegativity of the summed cost** from the two checks. -/
theorem sum_nonneg {φ : Cost} {nmax : ℕ} {Gcap : ℤ} {excl : List Row} {rows : List Row}
    (hrows : ∀ R ∈ rows, RowOK nmax Gcap excl R) (hc : φ.checkSmall nmax Gcap excl = true)
    (hbox : ∀ R, RowOK nmax Gcap excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ φ.aff R) :
    0 ≤ (rows.map φ.eval).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
  by_cases h7 : R.n ≤ 7 ∨ R.r ≤ 7
  · exact nonneg_of_checkSmall hc (hrows R hR) h7
  · push_neg at h7
    rw [eval_of_ge (by omega) (by omega)]
    exact hbox R (hrows R hR) (by omega) (by omega)

end Cost

/-- The flag numbers of the polar. -/
structure PolarRel (D Ds : FlagData) : Prop where
  v : Ds.v = D.h
  e : Ds.e = D.r
  p : Ds.p = D.p
  r : Ds.r = D.e
  h : Ds.h = D.v
  I : Ds.I = D.I
  x : Ds.x = D.y
  y : Ds.y = D.x
  f03 : Ds.f03 = D.f14
  f14 : Ds.f14 = D.f03

/-- The data of a putative counterexample with `v` vertices and `h` facets used by the
certificates: valid flag data, the facet rows of `P` and of its polar with their row facts. -/
structure Ctx (v h nF nS : ℕ) (excl exclS : List Row) where
  D : FlagData
  Ds : FlagData
  hD : D.Valid
  F : FacetRows D
  Fs : FacetRows Ds
  rel : PolarRel D Ds
  hv : D.v = v
  hh : D.h = h
  rowF : ∀ R ∈ F.rows, RowOK nF D.G excl R
  rowFs : ∀ R ∈ Fs.rows, RowOK nS D.Gs exclS R
  polyF : D.G = 0 → D.A = 0
  polyFs : D.Gs = 0 → D.A = 0
  evenF : ∀ q : Row → Bool, Even (F.rows.filter q).length
  evenFs : ∀ q : Row → Bool, Even (Fs.rows.filter q).length

namespace Ctx

variable {v h nF nS : ℕ} {excl exclS : List Row} (C : Ctx v h nF nS excl exclS)

/-- Count of facets of `P` with `n = k`. -/
abbrev nF5 : ℕ := Cost.cntN C.F.rows 5
abbrev nF6 : ℕ := Cost.cntN C.F.rows 6
abbrev rF5 : ℕ := Cost.cntR C.F.rows 5
abbrev rF6 : ℕ := Cost.cntR C.F.rows 6
abbrev nS5 : ℕ := Cost.cntN C.Fs.rows 5
abbrev nS6 : ℕ := Cost.cntN C.Fs.rows 6
abbrev rS5 : ℕ := Cost.cntR C.Fs.rows 5
abbrev rS6 : ℕ := Cost.cntR C.Fs.rows 6

/-- **Facet side**: a cost that is nonnegative on admissible rows gives a linear inequality. -/
theorem facet_ineq (φ : Cost) {G2 : ℤ} (hG : C.D.G ≤ G2) (hc : φ.checkSmall nF G2 excl = true)
    (hbox : ∀ R, RowOK nF G2 excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ φ.aff R) :
    0 ≤ φ.c0 * (C.D.h : ℤ) + φ.cn * (C.D.I : ℤ) + φ.ce * (C.D.f14 : ℤ) + φ.cp * (C.D.y : ℤ)
      + φ.cr * (2 * (C.D.r : ℤ)) + φ.cJ * (2 * (C.D.f03 : ℤ))
      + φ.a5 * (C.nF5 : ℤ) + φ.a6 * (C.nF6 : ℤ) + φ.b5 * (C.rF5 : ℤ) + φ.b6 * (C.rF6 : ℤ) := by
  have h1 := Cost.sum_nonneg (fun R hR => (C.rowF R hR).mono hG) hc hbox
  rw [Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r, C.F.sum_J] at h1
  push_cast at h1
  exact h1

/-- **Polar side**: the same for the facets of the polar (the vertex figures of `P`). -/
theorem polar_ineq (φ : Cost) {S2 : ℤ} (hS : C.D.Gs ≤ S2) (hc : φ.checkSmall nS S2 exclS = true)
    (hbox : ∀ R, RowOK nS S2 exclS R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ φ.aff R) :
    0 ≤ φ.c0 * (C.D.v : ℤ) + φ.cn * (C.D.I : ℤ) + φ.ce * (C.D.f03 : ℤ) + φ.cp * (C.D.x : ℤ)
      + φ.cr * (2 * (C.D.e : ℤ)) + φ.cJ * (2 * (C.D.f14 : ℤ))
      + φ.a5 * (C.nS5 : ℤ) + φ.a6 * (C.nS6 : ℤ) + φ.b5 * (C.rS5 : ℤ) + φ.b6 * (C.rS6 : ℤ) := by
  have h1 := Cost.sum_nonneg (fun R hR => (C.rowFs R hR).mono hS) hc hbox
  rw [Cost.sum_eval, C.Fs.length_eq, C.Fs.sum_n, C.Fs.sum_e, C.Fs.sum_p, C.Fs.sum_r, C.Fs.sum_J,
    C.rel.h, C.rel.I, C.rel.f14, C.rel.y, C.rel.r, C.rel.f03] at h1
  push_cast at h1
  exact h1

/-- **Facet side** without a cell bound on `G` (rows capped at `2g ≤ 1000`). -/
theorem facet_ineq_cap (φ : Cost) (hn : nF ≤ 11) (hc : φ.checkSmall nF 1000 excl = true)
    (hbox : ∀ R, RowOK nF 1000 excl R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ φ.aff R) :
    0 ≤ φ.c0 * (C.D.h : ℤ) + φ.cn * (C.D.I : ℤ) + φ.ce * (C.D.f14 : ℤ) + φ.cp * (C.D.y : ℤ)
      + φ.cr * (2 * (C.D.r : ℤ)) + φ.cJ * (2 * (C.D.f03 : ℤ))
      + φ.a5 * (C.nF5 : ℤ) + φ.a6 * (C.nF6 : ℤ) + φ.b5 * (C.rF5 : ℤ) + φ.b6 * (C.rF6 : ℤ) := by
  have h1 := Cost.sum_nonneg (fun R hR => (C.rowF R hR).capped hn) hc hbox
  rw [Cost.sum_eval, C.F.length_eq, C.F.sum_n, C.F.sum_e, C.F.sum_p, C.F.sum_r, C.F.sum_J] at h1
  push_cast at h1
  exact h1

/-- **Polar side** without a cell bound on `G*`. -/
theorem polar_ineq_cap (φ : Cost) (hn : nS ≤ 11) (hc : φ.checkSmall nS 1000 exclS = true)
    (hbox : ∀ R, RowOK nS 1000 exclS R → 8 ≤ R.n → 8 ≤ R.r → 0 ≤ φ.aff R) :
    0 ≤ φ.c0 * (C.D.v : ℤ) + φ.cn * (C.D.I : ℤ) + φ.ce * (C.D.f03 : ℤ) + φ.cp * (C.D.x : ℤ)
      + φ.cr * (2 * (C.D.e : ℤ)) + φ.cJ * (2 * (C.D.f14 : ℤ))
      + φ.a5 * (C.nS5 : ℤ) + φ.a6 * (C.nS6 : ℤ) + φ.b5 * (C.rS5 : ℤ) + φ.b6 * (C.rS6 : ℤ) := by
  have h1 := Cost.sum_nonneg (fun R hR => (C.rowFs R hR).capped hn) hc hbox
  rw [Cost.sum_eval, C.Fs.length_eq, C.Fs.sum_n, C.Fs.sum_e, C.Fs.sum_p, C.Fs.sum_r, C.Fs.sum_J,
    C.rel.h, C.rel.I, C.rel.f14, C.rel.y, C.rel.r, C.rel.f03] at h1
  push_cast at h1
  exact h1

/-- The global linear facts, with all flag numbers as integer atoms. -/
theorem lin :
    (C.D.v : ℤ) = v ∧ (C.D.h : ℤ) = h ∧
    (C.D.v : ℤ) - C.D.e + C.D.p - C.D.r + C.D.h = 2 ∧
    (C.D.f03 : ℤ) = C.D.I + C.D.x - 2 * C.D.e ∧
    (C.D.f14 : ℤ) = C.D.I + C.D.y - 2 * C.D.r ∧
    (C.D.f13 : ℤ) = C.D.I + C.D.x + C.D.y - 2 * (C.D.e + C.D.r) ∧
    (C.D.f024 : ℤ) = 2 * C.D.I + 2 * C.D.x + 2 * C.D.y - 4 * (C.D.e + C.D.r) ∧
    0 ≤ (C.D.f024 : ℤ) - 3 * C.D.x - 3 * C.D.y + 9 * C.D.p ∧
    0 ≤ 2 * (C.D.f13 : ℤ) - 3 * C.D.f03 ∧
    0 ≤ 2 * (C.D.f13 : ℤ) - 3 * C.D.f14 ∧
    2 * (C.D.I : ℤ) ≤ v * h ∧
    0 ≤ (C.D.e : ℤ) ∧ 0 ≤ (C.D.p : ℤ) ∧ 0 ≤ (C.D.r : ℤ) ∧ 0 ≤ (C.D.I : ℤ) ∧ 0 ≤ (C.D.x : ℤ) ∧
    0 ≤ (C.D.y : ℤ) ∧
    0 ≤ (C.nF5 : ℤ) ∧ 0 ≤ (C.nF6 : ℤ) ∧ 0 ≤ (C.rF5 : ℤ) ∧ 0 ≤ (C.rF6 : ℤ) ∧
    0 ≤ (C.nS5 : ℤ) ∧ 0 ≤ (C.nS6 : ℤ) ∧ 0 ≤ (C.rS5 : ℤ) ∧ 0 ≤ (C.rS6 : ℤ) := by
  have hD := C.hD
  have hinc : 2 * (C.D.I : ℤ) ≤ (C.D.v : ℤ) * C.D.h := by exact_mod_cast hD.incidence
  rw [C.hv, C.hh] at hinc
  refine ⟨by rw [C.hv], by rw [C.hh], hD.euler, hD.f03_eq, hD.f14_eq, hD.f13_eq, hD.f024_eq,
    hD.A_nonneg, hD.B_nonneg, hD.C_nonneg, by exact_mod_cast hinc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> positivity

lemma even_nF5 : Even C.nF5 := C.evenF _
lemma even_nF6 : Even C.nF6 := C.evenF _
lemma even_rS5 : Even C.rS5 := C.evenFs _
lemma even_rS6 : Even C.rS6 := C.evenFs _

lemma even_Gs : Even C.D.Gs := by
  obtain ⟨a, ha⟩ := C.hD.even_r; obtain ⟨b, hb⟩ := C.hD.even_y
  obtain ⟨c, hc⟩ := C.hD.even_p; obtain ⟨d, hd⟩ := C.hD.even_h
  refine ⟨a + b - 3 * c - 5 * d + 5, ?_⟩
  simp only [FlagData.Gs, ha, hb, hc, hd]; push_cast; ring

/-- `G` and `G*` as linear expressions. -/
lemma G_eq : C.D.G = (C.D.e : ℤ) + C.D.x - 3 * C.D.p - 5 * C.D.v + 10 := rfl
lemma Gs_eq : C.D.Gs = (C.D.r : ℤ) + C.D.y - 3 * C.D.p - 5 * C.D.h + 10 := rfl
lemma A_eq : C.D.A = (C.D.f024 : ℤ) - 3 * C.D.x - 3 * C.D.y + 9 * C.D.p := rfl
lemma t_eq : (C.D.t : ℤ) = C.D.e + C.D.r := by simp [FlagData.t]

end Ctx

end Kalai5
