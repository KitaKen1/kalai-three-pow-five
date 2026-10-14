import Kalai5.Foundations
import Kalai5.CubeSection
import Kalai5.Endpoints.Fourteen
import Kalai5.Endpoints.Sixteen
import Kalai5.Endpoints.FourteenM22
import Kalai5.Catalog.Small
import Kalai5.LemmaA.Final

/-!
# The remaining obligations, and the main theorem from them

`Obligations` lists, as precise Lean statements, everything that is not yet formalized.
`Obligations.mainClaim` proves Kalai's conjecture in dimension five from them, with no `sorry`.
So the whole remaining work is exactly to inhabit `Obligations`.

Groups of fields:
* foundations of polytope theory (face counting, Euler, flags, parity, `A, B, C ≥ 0`, incidences);
* rigidity: the centrally symmetric toric bound `G, G* ≥ 0` and stress localization;
* polarity, and the polar model of polytopes with at most twelve vertices (the combinatorial
  count itself is proved in `Kalai5.CubeSection`);
* facet rows and the Gale classification of 4-polytopes with at most seven vertices (the
  local inequalities on the 24 resulting rows are checked in `Kalai5.Catalog.Small`);
* the geometric "at most three full pairs" lemma at fourteen vertices;
* the twelve endpoints that are not yet reduced (`(14,20)`, `(14,24)`, `(14,26)` are derived here).
-/

namespace Kalai5

open Set

/-- Everything that is not yet formalized. -/
structure Obligations : Prop where
  /-- Every nonempty face has dimension `≤ 5` and `P` is the only `5`-face. -/
  faces_ncard : ∀ P, IsCSPolytope5 P → (faces P).ncard = (flagDataOf P).total
  /-- Euler–Poincaré relation. -/
  euler : ∀ P, IsCSPolytope5 P →
    (fvec P 0 : ℤ) - fvec P 1 + fvec P 2 - fvec P 3 + fvec P 4 = 2
  /-- Proper faces come in antipodal pairs. -/
  even_fvec : ∀ P, IsCSPolytope5 P → ∀ k ≤ 4, Even (fvec P k)
  /-- Flags of proper faces come in antipodal pairs. -/
  even_flag : ∀ P, IsCSPolytope5 P →
    Even (flag2 P 0 4) ∧ Even (flag2 P 0 2) ∧ Even (flag2 P 2 4)
  /-- Summed Euler in vertex figures. -/
  flag03 : ∀ P, IsCSPolytope5 P →
    (flag2 P 0 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 - 2 * fvec P 1
  /-- Summed Euler in facets. -/
  flag14 : ∀ P, IsCSPolytope5 P →
    (flag2 P 1 4 : ℤ) = flag2 P 0 4 + flag2 P 2 4 - 2 * fvec P 3
  /-- Summed Euler in 3-faces. -/
  flag13 : ∀ P, IsCSPolytope5 P →
    (flag2 P 1 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 + flag2 P 2 4 - 2 * (fvec P 1 + fvec P 3)
  /-- Summed Euler in vertex–facet intervals. -/
  flag024 : ∀ P, IsCSPolytope5 P →
    (flag3 P 0 2 4 : ℤ) = 2 * flag2 P 0 4 + 2 * flag2 P 0 2 + 2 * flag2 P 2 4
      - 4 * (fvec P 1 + fvec P 3)
  /-- `A ≥ 0`: polygons and polygonal face figures have at least three vertices. -/
  A_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).A
  /-- `B ≥ 0`: vertices of 3-polytopes have degree at least three. -/
  B_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).B
  /-- `C ≥ 0`: the polar statement of `B ≥ 0`. -/
  C_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).C
  /-- A facet contains at most one vertex of every antipodal pair. -/
  incidence : ∀ P, IsCSPolytope5 P → 2 * flag2 P 0 4 ≤ fvec P 0 * fvec P 4
  /-- Centrally symmetric toric bound (SWZ Thm 2.1; via rigidity, SWZ Thm 2.3). -/
  G_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).G
  /-- Its polar form. -/
  Gs_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).Gs
  /-- Polarity. -/
  polar : ∀ P, IsCSPolytope5 P → ∃ Q, IsCSPolytope5 Q ∧
    (faces Q).ncard = (faces P).ncard ∧ fvec Q 0 = fvec P 4 ∧ fvec Q 4 = fvec P 0
  /-- At most twelve vertices: the polar is a central section of the 6-cube. -/
  smallModel : ∀ P, IsCSPolytope5 P → fvec P 0 ≤ 12 →
    ∃ a : Fin 6 → ℝ, (∀ i, 0 ≤ a i) ∧ (faces P).ncard = sectionFaceCount a
  /-- Facet rows: one row per facet. -/
  rows_length : ∀ P, IsCSPolytope5 P → (facetRows P).length = fvec P 4
  rows_sum_n : ∀ P, IsCSPolytope5 P → ((facetRows P).map Row.n).sum = flag2 P 0 4
  rows_sum_e : ∀ P, IsCSPolytope5 P → ((facetRows P).map Row.e).sum = flag2 P 1 4
  rows_sum_p : ∀ P, IsCSPolytope5 P → ((facetRows P).map Row.p).sum = flag2 P 2 4
  /-- Every 3-face lies in exactly two facets. -/
  rows_sum_r : ∀ P, IsCSPolytope5 P → ((facetRows P).map Row.r).sum = 2 * fvec P 3
  rows_sum_J : ∀ P, IsCSPolytope5 P → ((facetRows P).map Row.J).sum = 2 * flag2 P 0 3
  /-- Facets are 4-polytopes. -/
  rows_real : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P, IsRealRow R
  /-- A facet has at most one vertex of every antipodal pair. -/
  rows_n_le : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P, 2 * R.n ≤ fvec P 0
  /-- Antipodal facets have the same row. -/
  rows_filter_even : ∀ P, IsCSPolytope5 P → ∀ q : Row → Bool, Even ((facetRows P).filter q).length
  /-- Stress localization `G ≥ 2 g(F)` (rigidity). -/
  stress_localization : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P, 2 * R.g ≤ (flagDataOf P).G
  /-- Gale classification: a 4-polytope with at most seven vertices has one of the 24 rows. -/
  small_classification : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows
  /-- Fourteen vertices, at least four full pairs: at least 243 faces (lemmas 18.1 and 24.1). -/
  fourteen_full : ∀ P, IsCSPolytope5 P → fvec P 0 = 14 → 18 ≤ fvec P 4 →
    8 ≤ ((facetRows P).filter fun R => R.n = 7).length → 243 ≤ (faces P).ncard
  /-- At `(14,22)` no facet has row `(7,15,14,6; 29)`: such a facet is a full pyramid, `P` is
  then the linear image of a bipyramid over a centrally symmetric 4-polytope, and
  `f₄(P) = 2 f₃(R) ≡ 0 (mod 4)` (bundle `kalai5_audit_14_22`, lemmas 22.2–22.3, replaced here by a
  parity argument that avoids SWZ Thm 1.1). -/
  full_pyramid_14 : ∀ P, IsCSPolytope5 P → fvec P 0 = 14 → fvec P 4 = 22 →
    excRow ∉ facetRows P
  /-- At sixteen vertices, a facet that is a prism over a tetrahedron (row `(8,16,14,6; 32)`)
  is full (one vertex of every antipodal pair), and then `P` has at least 243 faces: the four
  product-edge lines are parallel (projection onto the cross-polytope with segment fibres, the
  roof injection gives `3 · 81`) or concurrent (32 explicit vertices of the polar, so `f₄ ≥ 32`).
  Only the weak form `f₄ ≤ 29` is needed (bundle `kalai5_full_prism/full_prism_lemma.md`). -/
  full_prism_16 : ∀ P, IsCSPolytope5 P → fvec P 0 = 16 → fvec P 4 ≤ 29 →
    tRow ∈ facetRows P → 243 ≤ (faces P).ncard
  e16_16 : EndpointClaim 16 16
  e16_18 : EndpointClaim 16 18
  e16_20 : EndpointClaim 16 20
  e16_22 : EndpointClaim 16 22
  e18_18 : EndpointClaim 18 18
  e18_20 : EndpointClaim 18 20
  e18_22 : EndpointClaim 18 22
  e20_20 : EndpointClaim 20 20

namespace Obligations

section catalog

variable (O : Obligations) {R : Row} (hR : IsRealRow R) (hn : R.n ≤ 7)
include O hR hn

lemma catalog_L1 : 0 ≤ R.L1 := smallRows_L1 R (O.small_classification R hR hn)
lemma catalog_L2 : 0 ≤ R.L2 := smallRows_L2 R (O.small_classification R hR hn)
lemma catalog_L3 : 0 ≤ R.L3 := smallRows_L3 R (O.small_classification R hR hn)
lemma catalog_g : 0 ≤ R.g := smallRows_g R (O.small_classification R hR hn)

end catalog

variable (O : Obligations) {P : Set E5} (hP : IsCSPolytope5 P)
include O hP

/-- The flag data of an actual centrally symmetric 5-polytope is valid. -/
theorem valid : (flagDataOf P).Valid where
  euler := O.euler P hP
  even_v := O.even_fvec P hP 0 (by norm_num)
  even_e := O.even_fvec P hP 1 (by norm_num)
  even_p := O.even_fvec P hP 2 (by norm_num)
  even_r := O.even_fvec P hP 3 (by norm_num)
  even_h := O.even_fvec P hP 4 (by norm_num)
  even_I := (O.even_flag P hP).1
  even_x := (O.even_flag P hP).2.1
  even_y := (O.even_flag P hP).2.2
  f03_eq := O.flag03 P hP
  f14_eq := O.flag14 P hP
  f13_eq := O.flag13 P hP
  f024_eq := O.flag024 P hP
  A_nonneg := O.A_nonneg P hP
  B_nonneg := O.B_nonneg P hP
  C_nonneg := O.C_nonneg P hP
  G_nonneg := O.G_nonneg P hP
  Gs_nonneg := O.Gs_nonneg P hP
  incidence := O.incidence P hP

/-- The facet rows of an actual centrally symmetric 5-polytope. -/
noncomputable def rowsOf : FacetRows (flagDataOf P) where
  rows := facetRows P
  length_eq := O.rows_length P hP
  sum_n := O.rows_sum_n P hP
  sum_e := O.rows_sum_e P hP
  sum_p := O.rows_sum_p P hP
  sum_r := O.rows_sum_r P hP
  sum_J := O.rows_sum_J P hP

lemma n_le_seven (hv : fvec P 0 = 14) {R : Row} (hR : R ∈ facetRows P) : R.n ≤ 7 := by
  have := O.rows_n_le P hP R hR; omega

lemma n7_le_six (hv : fvec P 0 = 14) (hh : 18 ≤ fvec P 4)
    (hlt : (faces P).ncard < 243) :
    ((facetRows P).filter fun R => R.n = 7).length ≤ 6 := by
  have h8 : ¬ 8 ≤ ((facetRows P).filter fun R => R.n = 7).length :=
    fun h => absurd (O.fourteen_full P hP hv hh h) (by omega)
  obtain ⟨k, hk⟩ := O.rows_filter_even P hP fun R => R.n = 7
  omega

end Obligations

namespace Obligations

variable (O : Obligations)
include O

theorem endpoint_14_26 : EndpointClaim 14 26 := by
  intro P hP hv hh
  rw [O.faces_ncard P hP]
  exact closure_14_26 (O.valid hP) (O.rowsOf hP) hv hh fun R hR =>
    O.catalog_L1 (O.rows_real P hP R hR) (O.n_le_seven hP hv hR)

theorem endpoint_14_24 : EndpointClaim 14 24 := by
  intro P hP hv hh
  refine le_of_not_gt fun hlt => ?_
  have h6 := O.n7_le_six hP hv (by omega) hlt
  rw [O.faces_ncard P hP] at hlt
  exact absurd (closure_14_24 (O.valid hP) (O.rowsOf hP) hv hh (fun R hR =>
    O.catalog_L2 (O.rows_real P hP R hR) (O.n_le_seven hP hv hR)) h6) (by omega)

theorem endpoint_14_20 : EndpointClaim 14 20 := by
  intro P hP hv hh
  refine le_of_not_gt fun hlt => ?_
  have h6 := O.n7_le_six hP hv (by omega) hlt
  rw [O.faces_ncard P hP] at hlt
  exact absurd (closure_14_20 (O.valid hP) (O.rowsOf hP) hv hh
    (fun R hR => O.n_le_seven hP hv hR)
    (fun R hR => O.catalog_L3 (O.rows_real P hP R hR) (O.n_le_seven hP hv hR))
    (fun R hR => O.catalog_g (O.rows_real P hP R hR) (O.n_le_seven hP hv hR))
    (O.stress_localization P hP) h6) (by omega)

theorem endpoint_14_22 : EndpointClaim 14 22 := by
  intro P hP hv hh
  have hexc : excRow ∉ facetRows P := O.full_pyramid_14 P hP hv hh
  rw [O.faces_ncard P hP]
  exact closure_14_22_M22 (O.valid hP) (O.rowsOf hP) hv hh fun R hR =>
    smallRows_M22 R (O.small_classification R (O.rows_real P hP R hR) (O.n_le_seven hP hv hR))
      (fun h => hexc (h ▸ hR))

/-- `(14,18)` from the fourteen-vertex lemma: `G + G* + A = 2I - 8s + 26` and parity give
`I = f₀₄ ≥ 116`, so at least eight facets have seven vertices. -/
theorem endpoint_14_18 : EndpointClaim 14 18 := by
  intro P hP hv hh
  have hD := O.valid hP
  have hid := FlagData.GGA_identity hD
  have hG := hD.G_nonneg
  have hGs := hD.Gs_nonneg
  have hA := hD.A_nonneg
  obtain ⟨k, hk⟩ := hD.even_I
  have hI : (flagDataOf P).I = flag2 P 0 4 := rfl
  have hs : (flagDataOf P).s = fvec P 0 + fvec P 4 := rfl
  rw [hs, hv, hh, hI] at hid
  rw [hI] at hk
  have hsum := sum_n_le (facetRows P) fun R hR => O.n_le_seven hP hv hR
  rw [O.rows_sum_n P hP, O.rows_length P hP, hh] at hsum
  apply O.fourteen_full P hP hv (by omega)
  omega

/-- `(14,16)` from Lemma A: `G + G* + A = 2I - 8s + 26` and parity give `I = f₀₄ ≥ 108`, so at
least twelve facets have seven vertices; they give four independent full normals. -/
theorem endpoint_14_16 : EndpointClaim 14 16 := by
  intro P hP hv hh
  have hD := O.valid hP
  have hid := FlagData.GGA_identity hD
  have hG := hD.G_nonneg
  have hGs := hD.Gs_nonneg
  have hA := hD.A_nonneg
  obtain ⟨k, hk⟩ := hD.even_I
  have hI : (flagDataOf P).I = flag2 P 0 4 := rfl
  have hs : (flagDataOf P).s = fvec P 0 + fvec P 4 := rfl
  rw [hs, hv, hh, hI] at hid
  rw [hI] at hk
  have hsum := sum_n_le (facetRows P) fun R hR => O.n_le_seven hP hv hR
  rw [O.rows_sum_n P hP, O.rows_length P hP, hh] at hsum
  exact hP.three_pow_five_of_nine_full hv (by omega)

/-- `(16,24)`: `L1 ≥ 0` on every facet row except the full tetrahedron prism (`sum_L1`, Gale
rows and their duals, `J + 4n ≤ 4e`), which `full_prism_16` handles. -/
theorem endpoint_16_24 : EndpointClaim 16 24 := by
  intro P hP hv hh
  by_cases hT : tRow ∈ facetRows P
  · exact O.full_prism_16 P hP hv (by omega) hT
  rw [O.faces_ncard P hP]
  exact closure_16_24 (O.valid hP) (O.rowsOf hP) hv hh fun R hR =>
    L1_nonneg_of_le_eight O.small_classification (O.rows_real P hP R hR)
      (by have := O.rows_n_le P hP R hR; omega) (fun h => hT (h ▸ hR))

/-- All fifteen endpoints. -/
theorem endpoint (q : ℕ × ℕ) (hq : q ∈ ledger) : EndpointClaim q.1 q.2 := by
  simp only [ledger, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [O.endpoint_14_16, O.endpoint_14_18, O.endpoint_14_20, O.endpoint_14_22, O.endpoint_14_24, O.endpoint_14_26,
    O.e16_16, O.e16_18, O.e16_20, O.e16_22, O.endpoint_16_24, O.e18_18, O.e18_20, O.e18_22, O.e20_20]

/-- A polytope with fewer than 243 faces has at least 13 vertices (at-most-twelve theorem). -/
lemma thirteen_le (P : Set E5) (hP : IsCSPolytope5 P) (hlt : (faces P).ncard < 243) :
    13 ≤ fvec P 0 := by
  refine le_of_not_gt fun hle => ?_
  obtain ⟨a, ha, hc⟩ := O.smallModel P hP (by omega)
  have := le_sectionFaceCount_six a ha
  omega

/-- **Kalai's `3^d` conjecture for `d = 5`, from the obligations.** -/
theorem mainClaim : MainClaim := by
  intro P hP
  refine le_of_not_gt fun hlt => ?_
  obtain ⟨Q, hQ, hcQ, hQ0, hQ4⟩ := O.polar P hP
  have hv13 := O.thirteen_le P hP hlt
  have hh13 : 13 ≤ fvec P 4 := by have := O.thirteen_le Q hQ (by omega); omega
  have hvP := O.valid hP
  have hvQ := O.valid hQ
  obtain ⟨a, ha⟩ := hvP.even_v; obtain ⟨b, hb⟩ := hvP.even_h
  have e0 : (flagDataOf P).v = fvec P 0 := rfl
  have e4 : (flagDataOf P).h = fvec P 4 := rfl
  have f0 : (flagDataOf Q).v = fvec Q 0 := rfl
  have f4 : (flagDataOf Q).h = fvec Q 4 := rfl
  have htP : (flagDataOf P).total < 243 := by rw [← O.faces_ncard P hP]; exact hlt
  have htQ : (flagDataOf Q).total < 243 := by rw [← O.faces_ncard Q hQ]; omega
  rcases le_total (fvec P 0) (fvec P 4) with hvh | hhv
  · have hmem := FlagData.global_reduction hvP htP (by omega) (by omega) (by omega)
    exact absurd (O.endpoint _ hmem P hP rfl rfl) (by omega)
  · have hmem := FlagData.global_reduction hvQ htQ (by omega) (by omega) (by omega)
    exact absurd (O.endpoint _ hmem Q hQ rfl rfl) (by omega)

end Obligations

end Kalai5
