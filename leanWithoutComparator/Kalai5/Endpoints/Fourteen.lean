import Kalai5.LocalData
import Kalai5.Catalog.Small

/-!
# Closing arguments of the endpoints `(14,26)`, `(14,24)`, `(14,20)`

These are the counting parts of the endpoint proofs (MAIN_PROOF §5; bundle reports
`research/kalai5_audit_14_26`, `…_14_24`, `…_14_20`).  The inputs are stated as hypotheses:

* local inequalities `L1, L2, L3 ≥ 0` and `g ≥ 0` for the facet rows (from the Gale catalogue of
  4-polytopes with at most 7 vertices);
* `n ≤ 7` for every facet (a facet contains at most one vertex of each antipodal pair);
* at most six 7-vertex facets (`m ≤ 3` full pairs; geometric lemma of `(14,24)`/`(14,18)`);
* stress localization `G ≥ 2 g(F)` (rigidity, for `(14,20)` and `(14,22)`);
* for `(14,22)`: the classification of the rows into `smallRows`, and absence of the exceptional
  row `(7,15,14,6; 29)` (a facet with this row is a full pyramid, handled geometrically).
-/

namespace Kalai5

namespace FlagData

variable {D : FlagData}

lemma even_t (hD : D.Valid) : Even D.t := Even.add hD.even_e hD.even_r

/-- `t ≥ 120` means at least `243` nonempty faces. -/
lemma total_ge_of_t (hD : D.Valid) (ht : 120 ≤ D.t) : 243 ≤ D.total := by
  have h := total_eq hD
  omega

/-- `t ≥ 120` from a rational bound `t > 118` and parity. -/
lemma total_ge_of_t_gt (hD : D.Valid) (ht : 118 < D.t) : 243 ≤ D.total := by
  obtain ⟨k, hk⟩ := even_t hD
  exact total_ge_of_t hD (by omega)

lemma even_G (hD : D.Valid) : Even D.G := by
  obtain ⟨a, ha⟩ := hD.even_e; obtain ⟨b, hb⟩ := hD.even_x
  obtain ⟨c, hc⟩ := hD.even_p; obtain ⟨d, hd⟩ := hD.even_v
  refine ⟨a + b - 3 * c - 5 * d + 5, ?_⟩
  simp only [G, ha, hb, hc, hd]; push_cast; ring

end FlagData

variable {D : FlagData}

lemma sum_nonneg_of_rows {F : FacetRows D} {f : Row → ℤ} (h : ∀ R ∈ F.rows, 0 ≤ f R) :
    0 ≤ (F.rows.map f).sum :=
  List.sum_nonneg fun x hx => by
    obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx; exact h R hR

/-- **Endpoint (14,26)**: `L1 ≥ 0` on all facets closes the case. -/
theorem closure_14_26 (hD : D.Valid) (F : FacetRows D) (hv : D.v = 14) (hh : D.h = 26)
    (hL1 : ∀ R ∈ F.rows, 0 ≤ R.L1) : 243 ≤ D.total := by
  have hsum := F.sum_L1 hD
  have hpos := sum_nonneg_of_rows hL1
  have hA := hD.A_nonneg; have hG := hD.G_nonneg
  rw [hv, hh] at hsum
  apply FlagData.total_ge_of_t_gt hD
  have : (1434 : ℤ) ≤ 12 * D.t := by push_cast at hsum; linarith
  omega

/-- **Endpoint (14,24)**: `L2 ≥ 0` and at most six 7-vertex facets close the case. -/
theorem closure_14_24 (hD : D.Valid) (F : FacetRows D) (hv : D.v = 14) (hh : D.h = 24)
    (hL2 : ∀ R ∈ F.rows, 0 ≤ R.L2) (hn7 : (F.rows.filter fun R => R.n = 7).length ≤ 6) :
    243 ≤ D.total := by
  have hsum := F.sum_L2 hD
  have hpos := sum_nonneg_of_rows hL2
  have hA := hD.A_nonneg; have hG := hD.G_nonneg
  rw [hv, hh] at hsum
  apply FlagData.total_ge_of_t_gt hD
  have hn7' : ((F.rows.filter fun R => R.n = 7).length : ℤ) ≤ 6 := by exact_mod_cast hn7
  have : (714 : ℤ) ≤ 6 * D.t := by push_cast at hsum; linarith
  omega

lemma sum_n_le (rows : List Row) (hn : ∀ R ∈ rows, R.n ≤ 7) :
    (rows.map Row.n).sum ≤ 6 * rows.length + (rows.filter fun R => R.n = 7).length := by
  induction rows with
  | nil => simp
  | cons R rs ih =>
    have hR := hn R (List.mem_cons_self ..)
    have ih' := ih fun R' hR' => hn R' (List.mem_cons_of_mem _ hR')
    by_cases h7 : R.n = 7 <;> simp [List.filter_cons, h7] <;> omega

/-- **Endpoint (14,20)**: `L3 ≥ 0`, `g ≥ 0`, at most six 7-vertex facets and stress
localization close the case (the case `G = 0` uses `Σ g = 2G + 4v + 4h - f₀₄ - 8`). -/
theorem closure_14_20 (hD : D.Valid) (F : FacetRows D) (hv : D.v = 14) (hh : D.h = 20)
    (hn : ∀ R ∈ F.rows, R.n ≤ 7) (hL3 : ∀ R ∈ F.rows, 0 ≤ R.L3) (hg : ∀ R ∈ F.rows, 0 ≤ R.g)
    (hloc : ∀ R ∈ F.rows, 2 * R.g ≤ D.G)
    (hn7 : (F.rows.filter fun R => R.n = 7).length ≤ 6) : 243 ≤ D.total := by
  have hG := hD.G_nonneg
  obtain ⟨k, hk⟩ := FlagData.even_G hD
  rcases (show D.G = 0 ∨ 2 ≤ D.G by omega) with hG0 | hG2
  · -- `G = 0`: every facet is elementary, so `f₀₄ = 128`, but `f₀₄ ≤ 6·20 + 6`.
    exfalso
    have hzero : ∀ R ∈ F.rows, R.g = 0 := fun R hR => by
      have := hloc R hR; have := hg R hR; omega
    have hsum0 : (F.rows.map Row.g).sum = 0 := by
      rw [List.map_congr_left (g := fun _ => (0 : ℤ)) hzero]; simp
    have hsg := F.sum_g hD
    rw [hsum0, hG0, hv, hh] at hsg
    have hI := sum_n_le F.rows hn
    rw [F.sum_n, F.length_eq, hh] at hI
    push_cast at hsg
    omega
  · have hsum := F.sum_L3 hD
    have hpos := sum_nonneg_of_rows hL3
    have hA := hD.A_nonneg
    rw [hv] at hsum
    apply FlagData.total_ge_of_t_gt hD
    have hn7' : ((F.rows.filter fun R => R.n = 7).length : ℤ) ≤ 6 := by exact_mod_cast hn7
    have : (716 : ℤ) ≤ 6 * D.t := by push_cast at hsum; linarith
    omega

/-- The exceptional elementary seven-vertex row of `(14,22)`: a pyramid over a triangular prism. -/
def excRow : Row := ⟨7, 15, 14, 6, 29⟩

/-- Per-row weight used for `(14,22)`: `ψ = L3 - 12[n = 7] + 7n - 42`. -/
def psi22 (R : Row) : ℤ := R.L3 - (if R.n = 7 then 12 else 0) + 7 * R.n - 42

/-- On elementary non-exceptional catalogue rows, `ψ ≥ 0`. -/
lemma psi22_nonneg : ∀ R ∈ smallRows, R.g = 0 → R ≠ excRow → 0 ≤ psi22 R := by
  decide +kernel

lemma sum_psi22 (F : FacetRows D) (hD : D.Valid) :
    (F.rows.map psi22).sum = 6 * (D.t : ℤ) - 62 * D.v + 124 - 2 * D.A - 22 * D.G
      + 7 * D.I - 42 * D.h := by
  have hL3 := F.sum_L3 hD
  have hi := sum_map_ite F.rows (fun R => R.n = 7) (-12)
  have hlin := sum_map_linear F.rows 7 0 0 0 0 (-42)
  have hsplit : (F.rows.map psi22).sum = (F.rows.map Row.L3).sum
      + (F.rows.map fun R : Row => if R.n = 7 then (-12 : ℤ) else 0).sum
      + (F.rows.map fun R : Row => (7 : ℤ) * R.n + 0 * R.e + 0 * R.p + 0 * R.r + 0 * R.J + (-42)).sum := by
    rw [← List.sum_map_add, ← List.sum_map_add]; congr 1
    apply List.map_congr_left; intro R _; simp only [psi22]; split_ifs <;> ring
  rw [hsplit, hlin, hi, F.sum_n, F.length_eq]
  linarith

/-- **Endpoint (14,22)**, counting part (MAIN_PROOF §5, steps 22.1 and 22.4). -/
theorem closure_14_22 (hD : D.Valid) (F : FacetRows D) (hv : D.v = 14) (hh : D.h = 22)
    (hcls : ∀ R ∈ F.rows, R ∈ smallRows) (hloc : ∀ R ∈ F.rows, 2 * R.g ≤ D.G)
    (hexc : excRow ∉ F.rows) (hn7 : (F.rows.filter fun R => R.n = 7).length ≤ 6) :
    243 ≤ D.total := by
  have hG := hD.G_nonneg
  have hA := hD.A_nonneg
  obtain ⟨k, hk⟩ := FlagData.even_G hD
  have hg : ∀ R ∈ F.rows, 0 ≤ R.g := fun R hR => smallRows_g R (hcls R hR)
  rcases (show D.G = 0 ∨ 2 ≤ D.G by omega) with hG0 | hG2
  · -- `G = 0`: all facets elementary, `f₀₄ = 136`, and `Σ ψ ≥ 0` forces `t ≥ 120`.
    have hzero : ∀ R ∈ F.rows, R.g = 0 := fun R hR => by
      have := hloc R hR; have := hg R hR; omega
    have hsum0 : (F.rows.map Row.g).sum = 0 := by
      rw [List.map_congr_left (g := fun _ => (0 : ℤ)) hzero]; simp
    have hsg := F.sum_g hD
    rw [hsum0, hG0, hv, hh] at hsg
    have hpsi : 0 ≤ (F.rows.map psi22).sum := sum_nonneg_of_rows fun R hR =>
      psi22_nonneg R (hcls R hR) (hzero R hR) (fun h => hexc (h ▸ hR))
    rw [sum_psi22 F hD, hG0, hv, hh] at hpsi
    apply FlagData.total_ge_of_t_gt hD
    push_cast at hsg hpsi
    omega
  · -- `G ≥ 2`: `22G ≤ 6t - 744 + 12 n₇` is impossible with `n₇ ≤ 6` unless `t ≥ 120`.
    have hsum := F.sum_L3 hD
    have hpos := sum_nonneg_of_rows fun R hR => smallRows_L3 R (hcls R hR)
    rw [hv] at hsum
    apply FlagData.total_ge_of_t_gt hD
    have hn7' : ((F.rows.filter fun R => R.n = 7).length : ℤ) ≤ 6 := by exact_mod_cast hn7
    have : (716 : ℤ) ≤ 6 * D.t := by push_cast at hsum; linarith
    omega

end Kalai5
